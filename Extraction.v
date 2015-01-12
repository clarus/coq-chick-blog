Require Import ExtrOcamlBasic.
Require Import ExtrOcamlBigIntConv.
Require Import ExtrOcamlString.
Require Import ListString.All.
Require Import Computation.

Module OCaml.
  Module String.
    Parameter t : Type.
    Extract Constant t => "string".

    Parameter of_lstring : LString.t -> t.
    Extract Constant of_lstring => "OCaml.String.of_lstring".

    Parameter to_lstring : t -> LString.t.
    Extract Constant to_lstring => "OCaml.String.to_lstring".
  End String.
End OCaml.

Module Lwt.
  Parameter t : Type -> Type.
  Extract Constant t "'a" => "'a Lwt.t".

  Parameter ret : forall {A : Type}, A -> t A.
  Extract Constant ret => "Lwt.return".

  Parameter bind : forall {A B : Type}, t A -> (A -> t B) -> t B.
  Extract Constant bind => "Lwt.bind".

  Parameter join : t unit -> t unit -> t unit.
  Extract Constant join => "fun x y -> Lwt.join [x]".

  Parameter run : forall {A : Type}, t A -> A.
  Extract Constant run => "Lwt_main.run".

  Parameter printl : OCaml.String.t -> t unit.
  Extract Constant printl => "Lwt_io.printl".

  Parameter flush : t unit.
  Extract Constant flush => "Lwt_io.flush Lwt_io.stdout".

  Parameter nextRequest : t OCaml.String.t.
  Extract Constant nextRequest => "Lwt_react.E.next Http.requests".
End Lwt.

Definition log (message : LString.t) (handler : C.t) : Lwt.t C.t :=
  let message := OCaml.String.of_lstring message in
  Lwt.bind (Lwt.printl message) (fun _ =>
  Lwt.bind Lwt.flush (fun _ =>
  Lwt.ret handler)).

Definition httpRequest (handler : LString.t -> C.t) : Lwt.t C.t :=
  Lwt.bind Lwt.nextRequest (fun httpRequest =>
  Lwt.ret (handler (OCaml.String.to_lstring httpRequest))).

(*Parameter httpAnswer : Http.Answer.t -> (unit -> C.t) -> Lwt.t C.t.
Extract Constant httpAnswer => "...".*)
Definition httpAnswer (answer : Http.Answer.t) (handler : unit -> C.t)
  : Lwt.t C.t :=
  Lwt.ret C.Ret.

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

Parameter start_server : Lwt.t unit.
Extract Constant start_server => "Http.start_server 8008".

Parameter fixpoint : forall {A B : Type}, ((A -> Lwt.t B) -> A -> Lwt.t B) ->
  A -> Lwt.t B.
Extract Constant fixpoint => "
  let rec fix f x =
    f (fix f) x in
  fix".

Definition eval (x : C.t) : unit :=
  Lwt.run (Lwt.join start_server (fixpoint (fun f x =>
      Lwt.bind (eval_step x) (fun x =>
      match x with
      | None => Lwt.ret tt
      | Some x => f x
      end))
      x)).
