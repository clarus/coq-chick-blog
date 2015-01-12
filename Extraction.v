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

  Parameter run : forall {A : Type}, t A -> A.
  Extract Constant run => "Lwt_main.run".

  Parameter printl : OCaml.String.t -> t unit.
  Extract Constant printl => "Lwt_io.printl".
End Lwt.

Definition log (message : LString.t) (handler : C.t) : Lwt.t C.t :=
  let message := OCaml.String.of_lstring message in
  Lwt.bind (Lwt.printl message) (fun _ =>
  Lwt.ret handler).

Fixpoint eval (x : C.t) : Lwt.t unit :=
  match x with
  | C.Ret => Lwt.ret tt
  | C.Let Command.Log message handler =>
    let message := OCaml.String.of_lstring message in
    Lwt.bind (Lwt.printl message) (fun _ =>
    eval (handler tt))
  end.

Parameter main_loop : Lwt.t unit -> unit.
Extract Constant main_loop => "fun x ->
  ...".
