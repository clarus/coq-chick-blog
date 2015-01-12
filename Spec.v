Require Import Coq.Lists.List.
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

Definition index : FiniteRun.t.
  apply cons.
  apply (RunRequest.New (Http.Request.New Http.Request.Kind.Get [[]])).
  exact (Run.Ret Http.Answer.Index).
  exact nil.
Defined.
