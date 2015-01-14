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
  | Index (posts : list Post.Header.t)
  | PostShow (post : option Post.t)
  | PostEdit (post : option Post.t)
  | Args (args : list (LString.t * list LString.t)).
End Answer.
