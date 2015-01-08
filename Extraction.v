Require Import ListString.All.
Require Import Computation.

Module OCaml.
  Parameter log : forall {A : Type}, LString.t -> (unit -> A) -> A.
  Parameter async : forall {A : Type} (command : Command.t),
    Command.request command -> (Command.answer command -> A) -> A.
End OCaml.

Definition eval_step (x : C.t) : option C.t :=
  match x with
  | C.Ret => None
  | C.Let command request handler =>
    OCaml.async command request (fun answer => Some (handler answer))
  end.
