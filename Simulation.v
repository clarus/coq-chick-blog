Require Import Computation.

Module Run.
  CoInductive t : C.t -> Type :=
  | Ret : t C.Ret
  | Let : forall (command : Command.t) (request : Command.request command)
    (answer : Command.answer command)
    {handler : Command.answer command -> C.t}, t (handler answer) ->
    t (C.Let command request handler).
End Run.
