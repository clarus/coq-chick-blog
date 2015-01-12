Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import ListString.All.

Import ListNotations.
Local Open Scope char.

Module Request.
  Inductive t :=
  | Get (path : list LString.t) (args : list (LString.t * LString.t)).

  Fixpoint parse_arguments (arguments : list LString.t)
    : list (LString.t * LString.t) + LString.t :=
    match arguments with
    | [] | [[]] => inl []
    | argument :: arguments =>
      match LString.split argument "=" with
      | [k; v] =>
        Sum.bind (parse_arguments arguments) (fun arguments =>
        inl ((k, v) :: arguments))
      | _ => inr @@ LString.s "expected exactly one '=' sign"
      end
    end.

  Definition parse_path (path : LString.t) : list LString.t :=
    match path with
    | "/" :: path => LString.split path "/"
    | _ => LString.split path "/"
    end.

  Definition of_string (url : LString.t) : t + LString.t :=
    match LString.split url "?" with
    | [name] => inl @@ Get (parse_path name) []
    | [name; arguments] =>
      Sum.bind (parse_arguments @@ LString.split arguments "&") (fun arguments =>
      inl @@ Get (parse_path name) arguments)
    | _ => inr @@ LString.s "expected at most one question mark"
    end.
End Request.

Module Answer.
  Inductive t :=
  | Index
  | Users
  | Error.

  Definition to_string (page : t) : LString.t :=
    match page with
    | Index => LString.s "Welcome to the index page!"
    | Users => LString.s "This will be the list of users."
    | Error => LString.s "Error"
    end.
End Answer.
