Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import ListString.All.
Require Import Computation.
Require Http.
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

Module Controller.
  Definition _page (answer : Http.Answer.t) : C.t :=
    do! Command.HttpAnswer @ answer in
    C.Ret.

  Definition index : C.t :=
    _page Http.Answer.Index.

  Definition users : C.t :=
    _page Http.Answer.Users.

  Definition error : C.t :=
    _page Http.Answer.Error.
End Controller.

Module Router.
  Definition route (request : Http.Request.t) : C.t :=
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
  let! request := Command.HttpRequest @ tt in
  Router.route request.
