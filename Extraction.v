Require Import ExtrOcamlBasic.
Require Import ExtrOcamlBigIntConv.
Require Import ExtrOcamlString.
Require Import ListString.All.
Require Import Computation.

Module Lwt.
  Parameter t : Type -> Type.
  Extract Constant t "'a" => "'a Lwt.t".

  Parameter ret : forall {A : Type}, A -> t A.
  Extract Constant ret => "Lwt.return".

  Parameter bind : forall {A B : Type}, t A -> (A -> t B) -> t B.
  Extract Constant bind => "Lwt.bind".

  Parameter run : forall {A : Type}, t A -> A.
  Extract Constant run => "Lwt_main.run".

  Parameter eprintl : LString.t -> Lwt.t unit.
  Extract Constant eprintl => "Lwt_io.eprintl".
End Lwt.

Definition log (message : LString.t) (handler : C.t) : Lwt.t C.t :=
  Lwt.bind (Lwt.eprintl message) (fun _ => Lwt.ret handler).

Parameter httpRequest : (LString.t -> C.t) -> Lwt.t C.t.
Extract Constant httpRequest => "fun handler =>
  Lwt.bind (Lwt_react.E.next_event httpRequests) (fun httpRequest ->
  Lwt.return (handler httpRequest))".

Parameter httpAnswer : Http.Answer.t -> (unit -> C.t) -> Lwt.t C.t.

Definition eval_let (command : Command.t) : Command.request command ->
  (Command.answer command -> C.t) -> Lwt.t C.t :=
  match command return Command.request command ->
    (Command.answer command -> _) -> _ with
  | Command.Log => fun request handler => log request (handler tt)
  | Command.HttpRequest => fun _ handler => httpRequest (fun httpRequest =>
    let path := LString.split httpRequest "/" in
    handler (Http.Request.New Http.Request.Kind.Get path))
  | Command.HttpAnswer => fun request handler => httpAnswer request handler
  end.

Definition eval_step (x : C.t) : Lwt.t (option C.t) :=
  match x with
  | C.Ret => Lwt.ret None
  | C.Let command request handler =>
    Lwt.bind (eval_let command request handler) (fun x =>
    Lwt.ret (Some x))
  end.

Parameter fixpoint : forall {A B : Type}, ((A -> Lwt.t B) -> A -> Lwt.t B) ->
  A -> Lwt.t B.

Definition eval : C.t -> Lwt.t unit :=
  fixpoint (fun f x =>
    Lwt.bind (eval_step x) (fun x =>
    match x with
    | None => Lwt.ret tt
    | Some x => f x
    end)).
