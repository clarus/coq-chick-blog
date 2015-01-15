Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Http.

Module Raw.
  Record t := New {
    path : list LString.t;
    args : Http.Arguments.t;
    cookies : Http.Cookies.t }.
End Raw.

Module Path.
  (*Inductive t :=
  | Static (path : list LString.t)
  | Index.*)
  Definition t := list LString.t.
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
  New (Raw.path request)
    (Raw.args request)
    (Cookies.parse @@ Raw.cookies request).
