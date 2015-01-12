Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import ListString.All.

Import ListNotations.
Local Open Scope char.

Module Request.
  Inductive t :=
  | Get (path : list LString.t) (args : list (LString.t * list LString.t)).
End Request.

Module Answer.
  Inductive t :=
  | Error
  | Index
  | Users
  | Args (args : list (LString.t * list LString.t)).

  Definition to_string (page : t) : LString.t :=
    match page with
    | Error => LString.s "Error"
    | Index => LString.s "Welcome to the index page!"
    | Users => LString.s "This will be the list of users."
    | Args args =>
      let args := args |> List.map (fun (arg : _ * _) =>
        let (name, values) := arg in
        name ++ LString.s ": " ++ LString.join (LString.s ", ") values) in
      LString.join (LString.s "<br/>" ++ [LString.Char.n]) args
    end.
End Answer.
