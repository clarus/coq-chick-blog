Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Moment.All.
Require Answer.
Require Import Computation.
Require Http.
Require Import Model.
Require Request.

Import ListNotations.
Import C.Notations.
Local Open Scope string.
Local Open Scope list.

Definition posts_directory : LString.t :=
  LString.s "posts/".

Module Helpers.
  Definition post_header {A : Type} (post_url : LString.t)
    (k : option Post.Header.t -> C.t A) : C.t A :=
    call! posts := Command.ListPosts posts_directory in
    k @@ Option.bind posts (fun posts =>
    posts |> List.find (fun post =>
      LString.eqb (Post.Header.url post) post_url)).

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
End Helpers.

Module Controller.
  Definition not_found : C.t Answer.t :=
    C.Ret Answer.NotFound.

  Definition forbidden : C.t Answer.t :=
    C.Ret Answer.Forbidden.

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

  Definition static (path : list LString.t) : C.t Answer.t :=
    let mime_type := mime_type @@ List.last path (LString.s "") in
    let file_name := LString.join (LString.s "/") path in
    call! content := Command.ReadFile file_name in
    match content with
    | None => not_found
    | Some content => C.Ret @@ Answer.Static mime_type content
    end.

  Definition index (is_logged : bool) : C.t Answer.t :=
    call! posts := Command.ListPosts posts_directory in
    match posts with
    | None =>
      do_call! Command.Log (LString.s "Cannot open the " ++ posts_directory ++
        LString.s " directory.") in
      C.Ret @@ Answer.Public is_logged @@ Answer.Public.Index []
    | Some posts => C.Ret @@ Answer.Public is_logged @@
      Answer.Public.Index posts
    end.

  Definition login : C.t Answer.t :=
    C.Ret Answer.Login.

  Definition logout : C.t Answer.t :=
    C.Ret Answer.Logout.

  Definition post_show (is_logged : bool) (post_url : LString.t) : C.t Answer.t :=
    let! post := Helpers.post post_url in
    C.Ret @@ Answer.Public is_logged @@ Answer.Public.PostShow post_url post.

  Definition post_add (is_logged : bool) : C.t Answer.t :=
    if negb is_logged then
      forbidden
    else
      C.Ret @@ Answer.Private Answer.Private.PostAdd.

  Definition post_do_add (is_logged : bool) (args : Http.Arguments.t)
    : C.t Answer.t :=
    if negb is_logged then
      forbidden
    else
      let title := Http.Arguments.find args @@ LString.s "title" in
      let year := Http.Arguments.find args @@ LString.s "year" in
      let month := Http.Arguments.find args @@ LString.s "month" in
      let day := Http.Arguments.find args @@ LString.s "day" in
      match (title, year, month, day) with
      | (Some [title], Some [year], Some [month], Some [day]) =>
        let year := Moment.Date.Parse.zero_padded_year 4 year in
        let month := Moment.Date.Parse.zero_padded_month month in
        let day := Moment.Date.Parse.zero_padded_day day in
        match (year, month, day) with
        | (Some (year, []), Some (month, []), Some (day, [])) =>
          let date := Moment.Date.New year month day in
          let file_name := LString.s "posts/" ++ Moment.Date.Print.date date ++
            LString.s " " ++ title ++ LString.s ".html" in
          call! is_success := Command.UpdateFile file_name (LString.s "") in
          C.Ret @@ Answer.Private @@ Answer.Private.PostDoAdd is_success
        | _ => C.Ret @@ Answer.Private @@ Answer.Private.PostDoAdd false
        end
      | _ => C.Ret @@ Answer.Private @@ Answer.Private.PostDoAdd false
      end.

  Definition post_edit (is_logged : bool) (post_url : LString.t) : C.t Answer.t :=
    if negb is_logged then
      forbidden
    else
      let! post := Helpers.post post_url in
      C.Ret @@ Answer.Private @@ Answer.Private.PostEdit post_url post.

  Definition post_do_edit (is_logged : bool) (post_url : LString.t)
    (args : Http.Arguments.t) : C.t Answer.t :=
    if negb is_logged then
      forbidden
    else
      let! is_success : bool := fun k =>
        match Http.Arguments.find args @@ LString.s "content" with
        | Some [content] =>
          let! header := Helpers.post_header post_url in
          match header with
          | None => k false
          | Some header =>
            let file_name := posts_directory ++ Post.Header.file_name header in
            call! is_success : bool := Command.UpdateFile file_name content in
            k is_success
          end
        | _ => k false
        end in
      C.Ret @@ Answer.Private @@ Answer.Private.PostDoEdit post_url is_success.

  Definition post_do_delete (is_logged : bool) (post_url : LString.t)
    : C.t Answer.t :=
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
      C.Ret @@ Answer.Private @@ Answer.Private.PostDoDelete is_success.
End Controller.

Definition server (request : Request.Raw.t) : C.t Answer.t :=
  match request with
  | Request.Raw.New path args cookies =>
    do_call! Command.Log (LString.s "GET /" ++ LString.join (LString.s "/") path) in
    let path := List.map LString.to_string path in
    let is_logged := Http.Cookies.is_logged cookies in
    match path with
    | "static" :: _ => Controller.static (List.map LString.s path)
    | [] => Controller.index is_logged
    | ["login"] => Controller.login
    | ["logout"] => Controller.logout
    | ["posts"; command] =>
      match command with
      | "add" => Controller.post_add is_logged
      | "do_add" => Controller.post_do_add is_logged args
      | _ => Controller.not_found
      end
    | ["posts"; command; post_url] =>
      let post_url := LString.s post_url in
      match command with
      | "show" => Controller.post_show is_logged post_url
      | "edit" => Controller.post_edit is_logged post_url
      | "do_edit" => Controller.post_do_edit is_logged post_url args
      | "do_delete" => Controller.post_do_delete is_logged post_url
      | _ => Controller.not_found
      end
    | _ => Controller.not_found
    end
  end.

Require Extraction.
Definition main := Extraction.main server.
Extraction "extraction/chickBlog" main.
