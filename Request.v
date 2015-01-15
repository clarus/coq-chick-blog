Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Http.

Import ListNotations.
Local Open Scope string.

Module Raw.
  Record t := New {
    path : list LString.t;
    args : Http.Arguments.t;
    cookies : Http.Cookies.t }.
End Raw.

Module Path.
  Inductive t :=
  | NotFound
  | Static (path : list LString.t)
  | Index
  | Login | Logout
  | PostAdd | PostDoAdd
  | PostShow (post_url : LString.t)
  | PostEdit (post_url : LString.t)
  | PostDoEdit (post_url : LString.t)
  | PostDoDelete (post_url : LString.t).

  Definition parse (path : list LString.t) : t :=
    match List.map LString.to_string path with
    | "static" :: path => Static (List.map LString.s path)
    | [] => Index
    | ["login"] => Login
    | ["logout"] => Logout
    | ["posts"; command] =>
      match command with
      | "add" => PostAdd
      | "do_add" => PostDoAdd
      | _ => NotFound
      end
    | ["posts"; command; post_url] =>
      let post_url := LString.s post_url in
      match command with
      | "show" => PostShow post_url
      | "edit" => PostEdit post_url
      | "do_edit" => PostDoEdit post_url
      | "do_delete" => PostDoDelete post_url
      | _ => NotFound
      end
    | _ => NotFound
    end.
End Path.

Module Arguments.
  Definition t := Http.Arguments.t.
End Arguments.

Module Cookies.
  Inductive t :=
  | LoggedIn
  | LoggedOut.

  Definition is_logged (cookies : t) : bool :=
    match cookies with
    | LoggedIn => true
    | LoggedOut => false
    end.

  Definition parse (cookies : Http.Cookies.t) : t :=
    match Http.Cookies.find cookies @@ LString.s "is_logged" with
    | Some is_logged =>
      if LString.eqb is_logged @@ LString.s "true" then
        LoggedIn
      else
        LoggedOut
    | None => LoggedOut
    end.
End Cookies.

Record t := New {
  path : Path.t;
  args : Arguments.t;
  cookies : Cookies.t }.

Definition parse (request : Raw.t) : t :=
  New (Path.parse @@ Raw.path request)
    (Raw.args request)
    (Cookies.parse @@ Raw.cookies request).
