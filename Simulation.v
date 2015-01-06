Require Import Computation.

Module Run.
  CoInductive t : C.t -> Type :=
  | Ret : t C.Ret
  | Let : forall {input output : Type} (i : input) (o : output)
    {handler : input -> C.t}, t (handler i) -> t (C.Let input o handler).

  Definition do {output : Type} (o : output) {handler : unit -> C.t}
    (handler_run : t (handler tt)) : t (C.Let _ _ _) :=
    Let tt o handler_run.
End Run.
