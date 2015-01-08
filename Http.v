Require Import ListString.All.

Module Request.
  Module Kind.
    Inductive t :=
    | Get
    | Post.
  End Kind.

  Record t := New {
    kind : Kind.t;
    url : list LString.t;
    args : list (LString.t * LString.t) }.
End Request.

Module Answer.
  Inductive t :=
  | Index
  | Users
  | Error.

  Definition to_string (page : t) : LString.t :=
    match page with
    | Index => LString.s "Welcome to the index page!"
    | Users => LString.s "This will be the list of users."
    | Error => LString.s "Error"
    end.
End Answer.
