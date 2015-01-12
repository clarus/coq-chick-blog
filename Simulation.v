Require Import Computation.

Module Run.
  Inductive t {A : Type} : C.t A -> Type :=
  | Ret : forall {x : A}, t (C.Ret x)
  | Let : forall (command : Command.t) (request : Command.request command)
    (answer : Command.answer command)
    {handler : Command.answer command -> C.t A}, t (handler answer) ->
    t (C.Let command request handler).
End Run.
