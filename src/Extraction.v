(** Extraction to OCaml. New primitives are defined in `extraction/utils.ml`. *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlBigIntConv.
Require Import ExtrOcamlString.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Computation.
Require Import Model.
Require Render.
Require Request.
Require Response.

Import ListNotations.
Local Open Scope type.

(** Interface with the OCaml strings. *)
Module String.
  (** The OCaml `string` type. *)
  Parameter t : Type.
  Extract Constant t => "string".

  (** Export to an OCaml string. *)
  Parameter of_lstring : LString.t -> t.
  Extract Constant of_lstring => "Utils.String.of_lstring".

  (** Import an OCaml string. *)
  Parameter to_lstring : t -> LString.t.
  Extract Constant to_lstring => "Utils.String.to_lstring".
End String.

(** Unbounded integers. *)
Module BigInt.
  (** The OCaml's `bigint` type. *)
  Definition t : Type := bigint.

  (** Export to a `Z`. *)
  Definition to_Z : t -> Z := z_of_bigint.
End BigInt.

(** Interface to the Lwt library. *)
Module Lwt.
  (** The `Lwt.t` type. *)
  Parameter t : Type -> Type.
  Extract Constant t "'a" => "'a Lwt.t".

  (** Return. *)
  Parameter ret : forall {A : Type}, A -> t A.
  Extract Constant ret => "Lwt.return".

  (** Bind. *)
  Parameter bind : forall {A B : Type}, t A -> (A -> t B) -> t B.
  Extract Constant bind => "Lwt.bind".

  (** Run. *)
  Parameter run : forall {A : Type}, t A -> A.
  Extract Constant run => "Lwt_main.run".

  (** Print a new line. *)
  Parameter printl : String.t -> t unit.
  Extract Constant printl => "Lwt_io.printl".

  (** The the content of a file. *)
  Parameter read_file : String.t -> t (option String.t).
  Extract Constant read_file => "Utils.read_file".

  (** Update (or create) a file with some content. *)
  Parameter update_file : String.t -> String.t -> t bool.
  Extract Constant update_file => "Utils.update_file".

  (** Delete a file. *)
  Parameter delete_file : String.t -> t bool.
  Extract Constant delete_file => "Utils.delete_file".

  (** List the files of a directory. *)
  Parameter list_files : String.t -> t (option (list String.t)).
  Extract Constant list_files => "Utils.list_files".
End Lwt.

(** Parse a list of files to a list of post headers. *)
Definition list_posts (directory : LString.t)
  : Lwt.t (option (list Post.Header.t)) :=
  Lwt.bind (Lwt.list_files @@ String.of_lstring directory) (fun file_names =>
  Lwt.ret @@ file_names |> option_map (fun file_names =>
  let posts := file_names |> List.map (fun file_name =>
    Post.Header.of_file_name @@ String.to_lstring file_name) in
  (* We remove the `None` elements. *)
  List.fold_left (fun posts post =>
    match post with
    | None => posts
    | Some post => post :: posts
    end)
    posts [])).

Definition eval_command (c : Command.t) : Lwt.t (Command.answer c) :=
  match c return Lwt.t (Command.answer c) with
  | Command.ReadFile file_name =>
    Lwt.bind (Lwt.read_file @@ String.of_lstring file_name) (fun content =>
    Lwt.ret @@ Option.map content String.to_lstring)
  | Command.UpdateFile file_name content =>
    let file_name := String.of_lstring file_name in
    let content := String.of_lstring content in
    Lwt.update_file file_name content
  | Command.DeleteFile file_name =>
    Lwt.delete_file @@ String.of_lstring file_name
  | Command.ListPosts directory => list_posts directory
  | Command.Log message =>
    Lwt.bind (Lwt.printl @@ String.of_lstring message) (fun _ =>
    Lwt.ret tt)
  end.

(** Evaluate a Coq computation to an Lwt expression. *)
Fixpoint eval {A : Type} (x : C.t A) : Lwt.t A :=
  match x with
  | C.Ret x => Lwt.ret x
  | C.Call c handler =>
    Lwt.bind (eval_command c) (fun answer => eval (handler answer))
  end.

(** Requests as given by CoHTTP using OCaml strings. *)
Module RawRequest.
  (** A request is an url, a list of arguments and some cookies. *)
  Definition t := list String.t * list (String.t * list String.t) *
    list (String.t * String.t).

  (** Import a request importing OCaml strings. *)
  Definition import (request : t) : Request.Raw.t :=
    match request with
    | (path, args, cookies) =>
      let path := List.map String.to_lstring path in
      let args := args |> List.map (fun (arg : _ * _) =>
        let (name, values) := arg in
        (String.to_lstring name, List.map String.to_lstring values)) in
      let cookies := cookies |> List.map (fun (cookie : _ * _) =>
        let (key, v) := cookie in
        (String.to_lstring key, String.to_lstring v)) in
      Request.Raw.New path args cookies
    end.
End RawRequest.

(** Responses as given to CoHTTP using OCaml strings. *)
Module RawResponse.
  (** An response a MIME type, some cookies and a body. *)
  Definition t := String.t * list (String.t * String.t) * String.t.

  (** Export a raw request exporting OCaml strings. *)
  Definition export (response : Response.Raw.t) : t :=
    let mime_type := String.of_lstring @@ Response.Raw.mime_type response in
    let cookies := Response.Raw.cookies response |> List.map (fun (cookie : _ * _) =>
      let (k, v) := cookie in
      (String.of_lstring k, String.of_lstring v)) in
    let content := String.of_lstring @@ Response.Raw.content response in
    (mime_type, cookies, content).
End RawResponse.

(** The infinite loop around the server handler. *)
Parameter main_loop : (RawRequest.t -> Lwt.t RawResponse.t) -> unit.
Extract Constant main_loop => "fun handler ->
  Lwt_main.run (Utils.start_server handler 8008)".

(** The function to extract to OCaml, parametrized by the server handler. *)
Definition main (handler : Request.Path.t -> Request.Cookies.t-> C.t Response.t)
  : unit :=
  main_loop (fun request =>
    let (path, cookies) := Request.parse @@ RawRequest.import request in
    Lwt.bind (eval @@ handler path cookies) (fun response =>
    Lwt.ret @@ RawResponse.export @@ Render.raw response)).
