Require Import ListString.All.

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
