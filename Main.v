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
  Definition index : C.t Http.Answer.t :=
    C.Ret Http.Answer.Index.

  Definition users : C.t Http.Answer.t :=
    C.Ret Http.Answer.Users.

  Definition error : C.t Http.Answer.t :=
    C.Ret Http.Answer.Error.
End Controller.

Definition server (request : Http.Request.t) : C.t Http.Answer.t :=
  let (kind, path) := request in
  match path with
  | [] => Controller.error
  | [[]] => Controller.index
  | dir :: path =>
    if LString.eqb dir (LString.s "users") then
      match path with
      | [] => Controller.users
      | _ => Controller.error
      end
    else
      Controller.error
  end.

Require Extraction.
Definition main := Extraction.main server.
Extraction "extraction/microBlog" main.
