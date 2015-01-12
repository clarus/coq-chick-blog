Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Computation.
Require Http.
Require Table.

Import ListNotations.
Import C.Notations.
Local Open Scope string.

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
  Definition error : C.t Http.Answer.t :=
    C.Ret Http.Answer.Error.

  Definition index : C.t Http.Answer.t :=
    C.Ret Http.Answer.Index.

  Definition users : C.t Http.Answer.t :=
    C.Ret Http.Answer.Users.

  Definition args (args : list (LString.t * list LString.t))
    : C.t Http.Answer.t :=
    C.Ret @@ Http.Answer.Args args.
End Controller.

Definition server (request : Http.Request.t) : C.t Http.Answer.t :=
  match request with
  | Http.Request.Get path args =>
    match List.map LString.to_string path with
    | [] => Controller.error
    | [""] => Controller.index
    | ["users"] => Controller.users
    | ["args"] => Controller.args args
    | _ => Controller.error
    end
  end.

Require Extraction.
Definition main := Extraction.main server.
Extraction "extraction/microBlog" main.
