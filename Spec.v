Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Computation.
Require Http.
Require Main.
Require Import Model.
Require Request.

Import ListNotations.
Local Open Scope char.

Module Run.
  Inductive t {A : Type} : C.t A -> Type :=
  | Ret : forall (x : A), t (C.Ret x)
  | Call : forall (command : Command.t) (answer : Command.answer command)
    {handler : Command.answer command -> C.t A}, t (handler answer) ->
    t (C.Call command handler).
End Run.

Module RunRequest.
  Inductive t :=
  | New : forall (request : Request.t), Run.t (Main.server request) -> t.
End RunRequest.

Module FiniteRun.
  Definition t := list RunRequest.t.
End FiniteRun.

Definition index (cookies : Request.Cookies.t)
  (post_headers : list Post.Header.t) : RunRequest.t.
  apply (RunRequest.New (Request.New Request.Path.Index cookies)).
  unfold Main.server; simpl.
  unfold Main.Controller.index; simpl.
  apply (Run.Call (Command.ListPosts _ ) (Some post_headers)).
  exact (Run.Ret (Answer.Public
    (Request.Cookies.is_logged @@ cookies)
    (Answer.Public.Index post_headers))).
Defined.
