Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import ListString.All.
Require Import Computation.
Require Table.

Import ListNotations.
Import C.Notations.

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
    Inductive t :=
    | Get
    | Post.
  End Kind.

  Record t := New {
    kind : Kind.t;
    url : list LString.t;
    args : list (LString.t * LString.t) }.
End Request.

Module Page.
  Inductive t :=
  | Index
  | Users
  | Error.
End Page.

Module Controller.
  Definition index : C.t :=
    do! Page.Index in
    C.Ret.

  Definition users : C.t :=
    do! Page.Users in
    C.Ret.

  Definition error : C.t :=
    do! Page.Error in
    C.Ret.
End Controller.

Module Router.
  Definition route (request : Request.t) : C.t :=
    let (kind, path, args) := request in
    match path with
    | [] => Controller.index
    | dir :: path =>
      if LString.eqb dir (LString.s "users") then
        match path with
        | [] => Controller.users
        | _ => Controller.error
        end
      else
        Controller.error
    end.
End Router.

CoFixpoint server : C.t :=
  let! request : Request.t := tt in
  Router.route request.
