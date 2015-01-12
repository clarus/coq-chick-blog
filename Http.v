Require Import ListString.All.

Module Request.
  Inductive t :=
  | Get (path : list LString.t) (args : list (LString.t * list LString.t)).
End Request.

Module Answer.
  Inductive t :=
  | Error
  | Static (mime_type : LString.t) (content : LString.t)
  | Index
  | Users
  | Args (args : list (LString.t * list LString.t)).
End Answer.
