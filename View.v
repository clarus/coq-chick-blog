Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Http.

Import ListNotations.
Local Open Scope char.

Definition to_string (page : Http.Answer.t) : LString.t :=
  match page with
  | Http.Answer.Error => LString.s "Error"
  | Http.Answer.Index => LString.s "Welcome to the index page!"
  | Http.Answer.Users => LString.s "This will be the list of users."
  | Http.Answer.Args args =>
    let args := args |> List.map (fun (arg : _ * _) =>
      let (name, values) := arg in
      name ++ LString.s ": " ++ LString.join (LString.s ", ") values) in
    LString.join (LString.s "<br/>" ++ [LString.Char.n]) args
  end.
