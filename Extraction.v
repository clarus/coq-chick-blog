Require Import ExtrOcamlBasic.
Require Import ExtrOcamlBigIntConv.
Require Import ExtrOcamlString.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Computation.
Require Http.

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

Fixpoint eval {A : Type} (x : C.t A) : Lwt.t A :=
  match x with
  | C.Ret x => Lwt.ret x
  | C.Let Command.Log message handler =>
    let message := OCaml.String.of_lstring message in
    Lwt.bind (Lwt.printl message) (fun _ =>
    eval (handler tt))
  end.

Parameter main_loop :
  (list OCaml.String.t -> list (OCaml.String.t * list OCaml.String.t) -> Lwt.t OCaml.String.t) ->
  unit.
Extract Constant main_loop => "fun handler ->
  Lwt_main.run (Http.start_server handler 8008)".

Definition main (handler : Http.Request.t -> C.t Http.Answer.t) : unit :=
  main_loop (fun path args =>
    let path := List.map OCaml.String.to_lstring path in
    let args := args |> List.map (fun (arg : _ * _) =>
      let (name, values) := arg in
      (OCaml.String.to_lstring name, List.map OCaml.String.to_lstring values)) in
    let request := Http.Request.Get path args in
    Lwt.bind (eval @@ handler request) (fun answer =>
    Lwt.ret @@ OCaml.String.of_lstring @@ Http.Answer.to_string answer)).
