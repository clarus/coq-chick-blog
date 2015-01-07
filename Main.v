Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import ListString.All.
Require Import Computation.
Require Page.
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

Module Controller.
  Definition _static (page : Page.t) : C.t :=
    do! page in
    C.Ret.

  Definition index : C.t :=
    _static Page.Index.

  Definition users : C.t :=
    _static Page.Users.

  Definition error : C.t :=
    _static Page.Error.
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
