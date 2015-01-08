(** The definition of computations, used to represent interactive programs. *)
Require Import ListString.All.
Require Http.

Module Command.
  Inductive t :=
  | Log
  | HttpRequest
  | HttpAnswer.

  Definition request (command : t) : Type :=
    match command with
    | Log => LString.t
    | HttpRequest => unit
    | HttpAnswer => Http.Answer.t
    end.

  Definition answer (command : t) : Type :=
    match command with
    | Log => unit
    | HttpRequest => Http.Request.t
    | HttpAnswer => unit
    end.
End Command.

Module C.
  CoInductive t : Type :=
  | Ret : t
  | Let : forall (command : Command.t), Command.request command ->
    (Command.answer command -> t) -> t.

  Definition step (c : t) : t :=
    match c with
    | Ret => Ret
    | Let command request handler => Let command request handler
    end.

  Lemma step_eq (c : t) : c = step c.
    destruct c; reflexivity.
  Qed.

  Module Notations.
    Notation "'let!' answer ':=' command '@' request 'in' X" :=
      (Let command request (fun answer => X))
      (at level 200, answer ident, request at level 100, command at level 100, X at level 200).

    Notation "'do!' command '@' request 'in' X" :=
      (Let command request (fun _ => X))
      (at level 200, request at level 100, command at level 100, X at level 200).

    (*Notation "'let!' i ':' I ':=' o 'in' X" := (Let I o (fun i => X))
      (at level 200, i ident, I at level 100, o at level 100, X at level 200).

    Notation "'do!' o 'in' X" := (Let unit o (fun _ => X))
      (at level 200, o at level 100, X at level 200).*)
  End Notations.
End C.
