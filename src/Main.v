(** The main function (the server handler) and the controller. *)
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Moment.All.
Require Import Computation.
Require Http.
Require Import Model.
Require Request.
Require Response.

Import ListNotations.
Import C.Notations.
Local Open Scope char.
Local Open Scope string.
Local Open Scope list.

(** The directory where posts are saved. *)
Definition posts_directory : LString.t :=
  LString.s "./".

(** Some helper functions for the controller. *)
Module Helpers.
  (** Try to find a post header from an URL. Expect a continuation (the next
      computation to do), since there is no bind in out language. *)
  Definition post_header {A : Type} (post_url : LString.t)
    (k : option Post.Header.t -> C.t A) : C.t A :=
    call! posts := Command.ListPosts posts_directory in
    k @@ Option.bind posts (fun posts =>
    posts |> List.find (fun post =>
      LString.eqb (Post.Header.url post) post_url)).

  (** Try to find a post from an URL. *)
  Definition post {A : Type} (post_url : LString.t)
    (k : option Post.t -> C.t A) : C.t A :=
    let! header := post_header post_url in
    match header with
    | None => k None
    | Some header =>
      let file_name := posts_directory ++ Post.Header.file_name header in
      call! content := Command.ReadFile file_name in
      k @@ Option.bind content (fun content =>
      Some (Post.New header content))
    end.

  (** Infer a MIME type from a file name. *)
  Definition mime_type (file_name : LString.t) : LString.t :=
    let extension := List.last (LString.split file_name ".") (LString.s "") in
    LString.s @@ match LString.to_string extension with
    | "html" => "text/html; charset=utf-8"
    | "css" => "text/css"
    | "js" => "text/javascript"
    | "png" => "image/png"
    | "svg" => "image/svg+xml"
    | _ => "text/plain"
    end.
End Helpers.

(** The controller. *)
Module Controller.
  (** Page not found. *)
  Definition not_found : C.t Response.t :=
    ret Response.NotFound.

  (** The arguments of the page cannot be parsed. *)
  Definition wrong_arguments : C.t Response.t :=
    ret Response.WrongArguments.

  (** The page cannot be accessed without login. *)
  Definition forbidden : C.t Response.t :=
    ret Response.Forbidden.

  (** A static file in the `static/` folder. *)
  Definition static (path : list LString.t) : C.t Response.t :=
    let mime_type := Helpers.mime_type @@ List.last path (LString.s "") in
    let file_name := LString.s "static/" ++ LString.join (LString.s "/") path in
    call! content := Command.ReadFile file_name in
    match content with
    | None => not_found
    | Some content => ret @@ Response.Static mime_type content
    end.

  (** The index page. *)
  Definition index (is_logged : bool) : C.t Response.t :=
    call! posts := Command.ListPosts posts_directory in
    match posts with
    | None =>
      do_call! Command.Log (LString.s "Cannot open the " ++ posts_directory ++
        LString.s " directory.") in
      ret @@ Response.Index is_logged []
    | Some posts => ret @@ Response.Index is_logged posts
    end.

  (** Confirmation that the user is logged in. *)
  Definition login (is_logged : bool) : C.t Response.t :=
    ret Response.Login.

  (** Confirmation that the user is logged out. *)
  Definition logout : C.t Response.t :=
    ret Response.Logout.

  (** Show the content of a post. *)
  Definition post_show (is_logged : bool) (post_url : LString.t) : C.t Response.t :=
    let! post := Helpers.post post_url in
    ret @@ Response.PostShow is_logged post_url post.

  (** Show the form to add a post. *)
  Definition post_add (is_logged : bool) : C.t Response.t :=
    if negb is_logged then
      forbidden
    else
      ret Response.PostAdd.

  (** Add a post and show a confirmation. *)
  Definition post_do_add (is_logged : bool) (title : LString.t)
    (date : Moment.Date.t) : C.t Response.t :=
    if negb is_logged then
      forbidden
    else
      let file_name := posts_directory ++ Moment.Date.Print.date date ++
        LString.s " " ++ title ++ LString.s ".html" in
      call! is_success := Command.UpdateFile file_name (LString.s "") in
      ret @@ Response.PostDoAdd is_success.

  (** Show the form to edit a post. *)
  Definition post_edit (is_logged : bool) (post_url : LString.t) : C.t Response.t :=
    if negb is_logged then
      forbidden
    else
      let! post := Helpers.post post_url in
      ret @@ Response.PostEdit post_url post.

  (** Edit a post and show a confirmation. *)
  Definition post_do_edit (is_logged : bool) (post_url : LString.t)
    (content : LString.t) : C.t Response.t :=
    if negb is_logged then
      forbidden
    else
      let! is_success : bool := fun k =>
        let! header := Helpers.post_header post_url in
        match header with
        | None => k false
        | Some header =>
          let file_name := posts_directory ++ Post.Header.file_name header in
          call! is_success : bool := Command.UpdateFile file_name content in
          k is_success
        end in
      ret @@ Response.PostDoEdit post_url is_success.

  (** Delete a post and show a confirmation. *)
  Definition post_do_delete (is_logged : bool) (post_url : LString.t)
    : C.t Response.t :=
    if negb is_logged then
      forbidden
    else
      let! is_success := fun k =>
        let! header := Helpers.post_header post_url in
        match header with
        | None => k false
        | Some header =>
          let file_name := posts_directory ++ Post.Header.file_name header in
          call! is_success : bool := Command.DeleteFile file_name in
          k is_success
        end in
      ret @@ Response.PostDoDelete is_success.
End Controller.

(** The main function, the server handler. *)
Definition server (path : Request.Path.t) (cookies : Request.Cookies.t)
  : C.t Response.t :=
  let is_logged := Request.Cookies.is_logged cookies in
  match path with
  | Request.Path.NotFound => Controller.not_found
  | Request.Path.WrongArguments => Controller.wrong_arguments
  | Request.Path.Static path => Controller.static path
  | Request.Path.Index => Controller.index is_logged
  | Request.Path.Login => Controller.login is_logged
  | Request.Path.Logout => Controller.logout
  | Request.Path.PostAdd => Controller.post_add is_logged
  | Request.Path.PostDoAdd title date =>
    Controller.post_do_add is_logged title date
  | Request.Path.PostShow post_url => Controller.post_show is_logged post_url
  | Request.Path.PostEdit post_url => Controller.post_edit is_logged post_url
  | Request.Path.PostDoEdit post_url content =>
    Controller.post_do_edit is_logged post_url content
  | Request.Path.PostDoDelete post_url =>
    Controller.post_do_delete is_logged post_url
  end.

(** Extract the server handler. *)
Require Extraction.
Definition main := Extraction.main server.
Extraction "extraction/chickBlog" main.
