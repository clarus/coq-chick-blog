Require Import Coq.NArith.NArith.
Require Import ListString.All.
Require Import Computation.
Require Table.

Module User.
  Record t := New {
    name : LString.t;
    email : LString.t }.
End User.

Module Users.
  Definition t := Table.t User.t.
End Users.

Module Post.
  Record t := New {
    user : N;
    content : LString.t }.
End Post.

Module Posts.
  Definition t := Table.t Post.t.
End Posts.

Module Request.
  Module Kind.
    Inductive t : Set :=
    | Get
    | Post.
  End Kind.

  Record t := New {
    kind : Kind.t;
    url : list LString.t;
    args : list (LString.t * LString.t) }.
End Request.

Module Router.
  Definition route (request : Request.t) : C.t :=
    C.Ret.
End Router.
