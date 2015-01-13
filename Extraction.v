Require Import ExtrOcamlBasic.
Require Import ExtrOcamlBigIntConv.
Require Import ExtrOcamlString.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Computation.
Require Http.
Require Import Model.
Require View.

Module String.
  Parameter t : Type.
  Extract Constant t => "string".

  Parameter of_lstring : LString.t -> t.
  Extract Constant of_lstring => "OCaml.String.of_lstring".

  Parameter to_lstring : t -> LString.t.
  Extract Constant to_lstring => "OCaml.String.to_lstring".
End String.

Module Lwt.
  Parameter t : Type -> Type.
  Extract Constant t "'a" => "'a Lwt.t".

  Parameter ret : forall {A : Type}, A -> t A.
  Extract Constant ret => "Lwt.return".

  Parameter bind : forall {A B : Type}, t A -> (A -> t B) -> t B.
  Extract Constant bind => "Lwt.bind".

  Parameter run : forall {A : Type}, t A -> A.
  Extract Constant run => "Lwt_main.run".

  Parameter printl : String.t -> t unit.
  Extract Constant printl => "Lwt_io.printl".

  Parameter read_file : String.t -> t (option String.t).
  Extract Constant read_file => "fun file_name ->
    Lwt.catch (fun _ ->
      Lwt.bind (Lwt_io.open_file Lwt_io.Input file_name) (fun channel ->
      Lwt.bind (Lwt_io.read channel) (fun content ->
      Lwt.return @@ Some content)))
      (fun _ -> Lwt.return None)".

  Parameter list_files : String.t -> t (option (list String.t)).
  Extract Constant list_files => "fun directory ->
    Lwt.catch (fun _ ->
      let files = Lwt_unix.files_of_directory directory in
      Lwt.bind (Lwt_stream.to_list files) (fun files ->
      Lwt.return @@ Some files))
      (fun _ -> Lwt.return None)".
End Lwt.

Module Model.
  Parameter users_get : unit -> list (String.t * (String.t * String.t)).
  Extract Constant users_get => "Model.users_get".
End Model.

Fixpoint eval {A : Type} (x : C.t A) : Lwt.t A :=
  match x with
  | C.Ret x => Lwt.ret x
  | C.Let (Command.FileRead file_name) handler =>
    let file_name := String.of_lstring file_name in
    Lwt.bind (Lwt.read_file file_name) (fun content =>
    eval @@ handler @@ option_map String.to_lstring content)
  | C.Let (Command.ListFiles directory) handler =>
    let directory := String.of_lstring directory in
    Lwt.bind (Lwt.list_files directory) (fun files =>
    let files := files |> option_map (fun files => files |> List.map String.to_lstring) in
    eval @@ handler files)
  | C.Let (Command.Log message) handler =>
    let message := String.of_lstring message in
    Lwt.bind (Lwt.printl message) (fun _ =>
    eval @@ handler tt)
  | C.Let Command.ModelGet handler =>
    let users := Model.users_get tt |> List.map (fun user =>
      match user with
      | (login, (password, email)) =>
        (String.to_lstring login,
          User.New (String.to_lstring password) (String.to_lstring email))
      end) in
    eval @@ handler users
  end.

Parameter main_loop :
  (list String.t -> list (String.t * list String.t) ->
    Lwt.t (String.t * String.t)) ->
  unit.
Extract Constant main_loop => "fun handler ->
  Lwt_main.run (Http.start_server handler 8008)".

Definition main (handler : Http.Request.t -> C.t Http.Answer.t) : unit :=
  main_loop (fun path args =>
    let path := List.map String.to_lstring path in
    let args := args |> List.map (fun (arg : _ * _) =>
      let (name, values) := arg in
      (String.to_lstring name, List.map String.to_lstring values)) in
    let request := Http.Request.Get path args in
    Lwt.bind (eval @@ handler request) (fun answer =>
    let mime_type := String.of_lstring @@ View.mime_type answer in
    let content := String.of_lstring @@ View.content answer in
    Lwt.ret (mime_type, content))).
