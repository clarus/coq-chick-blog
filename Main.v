Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Computation.
Require Http.
Require Import Model.

Import ListNotations.
Import C.Notations.
Local Open Scope string.
Local Open Scope list.

Module Controller.
  Definition posts_directory : LString.t :=
    LString.s "posts/".

  Definition not_found : C.t Http.Answer.t :=
    C.Ret Http.Answer.NotFound.

  Definition forbidden : C.t Http.Answer.t :=
    C.Ret Http.Answer.Forbidden.

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

  Definition static (path : list LString.t) : C.t Http.Answer.t :=
    let mime_type := mime_type @@ List.last path (LString.s "") in
    let file_name := LString.join (LString.s "/") path in
    let! content := Command.ReadFile file_name in
    match content with
    | None => not_found
    | Some content => C.Ret @@ Http.Answer.Static mime_type content
    end.

  Definition index (is_logged : bool) : C.t Http.Answer.t :=
    let! posts := Command.ListPosts posts_directory in
    match posts with
    | None =>
      do! Command.Log (LString.s "Cannot open the " ++ posts_directory ++
        LString.s " directory.") in
      C.Ret @@ Http.Answer.Public is_logged @@ Http.Answer.Public.Index []
    | Some posts => C.Ret @@ Http.Answer.Public is_logged @@
      Http.Answer.Public.Index posts
    end.

  Definition login : C.t Http.Answer.t :=
    C.Ret Http.Answer.Login.

  Definition logout : C.t Http.Answer.t :=
    C.Ret Http.Answer.Logout.

  Definition post_show (is_logged : bool) (post_url : LString.t) : C.t Http.Answer.t :=
    let! posts := Command.ListPosts posts_directory in
    match posts with
    | None => C.Ret @@ Http.Answer.Public is_logged @@ Http.Answer.Public.PostShow post_url None
    | Some posts =>
      let header := posts |> List.find (fun post =>
        LString.eqb (Post.Header.url post) post_url) in
      match header with
      | None => C.Ret @@ Http.Answer.Public is_logged @@ Http.Answer.Public.PostShow post_url None
      | Some header =>
        let file_name := posts_directory ++ Post.Header.file_name header in
        let! content := Command.ReadFile file_name in
        let post := content |> option_map (Post.New header) in
        C.Ret @@ Http.Answer.Public is_logged @@ Http.Answer.Public.PostShow post_url post
      end
    end.

  Definition post_add (is_logged : bool) : C.t Http.Answer.t :=
    if negb is_logged then
      forbidden
    else
      C.Ret @@ Http.Answer.Private Http.Answer.Private.PostAdd.

  Definition post_do_add (is_logged : bool) : C.t Http.Answer.t :=
    if negb is_logged then
      forbidden
    else
      C.Ret @@ Http.Answer.Private @@ Http.Answer.Private.PostDoAdd false.

  Definition post_edit (is_logged : bool) (post_url : LString.t) : C.t Http.Answer.t :=
    if negb is_logged then
      forbidden
    else
      let! posts := Command.ListPosts posts_directory in
      match posts with
      | None => C.Ret @@ Http.Answer.Private @@ Http.Answer.Private.PostEdit post_url None
      | Some posts =>
        let header := posts |> List.find (fun post =>
          LString.eqb (Post.Header.url post) post_url) in
        match header with
        | None => C.Ret @@ Http.Answer.Private @@ Http.Answer.Private.PostEdit post_url None
        | Some header =>
          let file_name := posts_directory ++ Post.Header.file_name header in
          let! content := Command.ReadFile file_name in
          let post := content |> option_map (Post.New header) in
          C.Ret @@ Http.Answer.Private @@ Http.Answer.Private.PostEdit post_url post
        end
      end.

  Definition post_do_edit (is_logged : bool) (post_url : LString.t) (args : Http.Arguments.t)
    : C.t Http.Answer.t :=
    if negb is_logged then
      forbidden
    else
      match Http.Arguments.find args @@ LString.s "content" with
      | Some [content] =>
        let! posts := Command.ListPosts posts_directory in
        match posts with
        | None => C.Ret @@ Http.Answer.Private @@ Http.Answer.Private.PostDoEdit post_url false
        | Some posts =>
          let header := posts |> List.find (fun post =>
            LString.eqb (Post.Header.url post) post_url) in
          match header with
          | None => C.Ret @@ Http.Answer.Private @@ Http.Answer.Private.PostDoEdit post_url false
          | Some header =>
            let file_name := posts_directory ++ Post.Header.file_name header in
            let! is_success := Command.UpdateFile file_name content in
            C.Ret @@ Http.Answer.Private @@ Http.Answer.Private.PostDoEdit post_url is_success
          end
        end
      | _ => C.Ret @@ Http.Answer.Private @@ Http.Answer.Private.PostDoEdit post_url false
      end.
End Controller.

Definition server (request : Http.Request.t) : C.t Http.Answer.t :=
  match request with
  | Http.Request.Get path args cookies =>
    do! Command.Log (LString.s "GET /" ++ LString.join (LString.s "/") path) in
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
      | "do_add" => Controller.post_do_add is_logged
      | _ => Controller.not_found
      end
    | ["posts"; command; post_url] =>
      let post_url := LString.s post_url in
      match command with
      | "show" => Controller.post_show is_logged post_url
      | "edit" => Controller.post_edit is_logged post_url
      | "do_edit" => Controller.post_do_edit is_logged post_url args
      | _ => Controller.not_found
      end
    | _ => Controller.not_found
    end
  end.

Require Extraction.
Definition main := Extraction.main server.
Extraction "extraction/chickBlog" main.
