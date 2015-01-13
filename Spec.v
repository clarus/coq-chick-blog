Require Import Coq.Lists.List.
Require Import ListString.All.
Require Import Computation.
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

(** Get one page and compare its result with `answer`. *)
Ltac static_page path args answer :=
  apply cons; [
  apply (RunRequest.New (Http.Request.Get path args));
  apply (Run.Let Command.Log _ tt);
  exact (Run.Ret answer) |
  exact nil].

Ltac static_page_no_args path answer :=
  static_page path (nil (A := LString.t * list LString.t)) answer.

Definition unknown_page : FiniteRun.t.
  static_page_no_args [LString.s "hello"] Http.Answer.Error.
Defined.

Definition index : FiniteRun.t.
  static_page_no_args ([] : list LString.t) Http.Answer.Index.
Defined.

Definition users : FiniteRun.t.
  static_page_no_args [LString.s "users"] (Http.Answer.Users []).
Defined.

Definition args (args : list (LString.t * list LString.t)) : FiniteRun.t.
  static_page [LString.s "args"] args (Http.Answer.Args args).
Defined.
