Require Import ListString.All.
Require Import Model.

Module Request.
  Inductive t :=
  | Get (path : list LString.t) (args : list (LString.t * list LString.t)).
End Request.

Module Answer.
  Inductive t :=
  | Error
  | Static (mime_type : LString.t) (content : LString.t)
  | Index (titles : list LString.t)
  | Users (users : Users.t)
  | Args (args : list (LString.t * list LString.t)).
End Answer.
