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
