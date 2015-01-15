Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Computation.
Require Http.
Require Main.
Require Request.

Import ListNotations.
Local Open Scope char.

Module Run.
  Inductive t {A : Type} : C.t A -> Type :=
  | Ret : forall (x : A), t (C.Ret x)
  | Call : forall (command : Command.t) (answer : Command.answer command)
    {handler : Command.answer command -> C.t A}, t (handler answer) ->
    t (C.Call command handler).
End Run.

Module RunRequest.
  Inductive t :=
  | New : forall (request : Request.t), Run.t (Main.server request) -> t.
End RunRequest.

Module FiniteRun.
  Definition t := list RunRequest.t.
End FiniteRun.

Definition index : RunRequest.t.
  apply (RunRequest.New (Request.Get [] [] [])).
  simpl.
  apply (Run.Call (Command.Log _) tt).
Admitted.

(*
(** Get one page and compare its result with `answer`. *)
Ltac static_page path args answer :=
  apply cons; [
  apply (RunRequest.New (Http.Request.Get path args));
  apply (Run.Let (Command.Log _) tt);
  exact (Run.Ret answer) |
  exact nil].

Ltac static_page_no_args path answer :=
  static_page path (nil (A := LString.t * list LString.t)) answer.

Definition unknown_page : FiniteRun.t.
  static_page_no_args [LString.s "hello"] Http.Answer.Error.
Defined.

Definition index (file_names : list LString.t) : FiniteRun.t.
  apply cons.
  - apply (RunRequest.New (Http.Request.Get [] [])).
    simpl.
    apply (Run.Let (Command.Log _) tt).
    unfold Main.Controller.index; simpl.
    apply (Run.Let (Command.ListFiles _) (Some file_names)).
    refine (let posts := file_names |> List.map (fun file_name =>
      Post.Header.New file_name (LString.s "date") file_name) in _).
    exact (Run.Ret (Http.Answer.Index posts)).
  - exact nil.
Defined.

Definition args (args : Arguments.t) : FiniteRun.t.
  static_page [LString.s "args"] args (Http.Answer.Args args).
Defined.*)
