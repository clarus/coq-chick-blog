Require Import Coq.Lists.List.
Require Import ListString.All.
Require Http.
Require Main.
Require Import Simulation.

Import ListNotations.

Module RunRequest.
  Inductive t :=
  | New : forall (request : Http.Request.t), Run.t (Main.server request) -> t.
End RunRequest.

Module FiniteRun.
  Definition t := list RunRequest.t.
End FiniteRun.

Ltac static_page path answer :=
  apply cons; [
  apply (RunRequest.New (Http.Request.Get path));
  exact (Run.Ret answer) |
  exact nil].

Definition index : FiniteRun.t.
  static_page [LString.s ""] Http.Answer.Index.
Defined.

Definition users : FiniteRun.t.
  static_page [LString.s "users"] Http.Answer.Users.
Defined.

Definition unknown_page : FiniteRun.t.
  static_page [LString.s "hello"] Http.Answer.Error.
Defined.
