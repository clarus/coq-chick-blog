(** The definition of computations, used to represent interactive programs. *)
Require Import ListString.All.
Require Import Model.

Local Open Scope type.

Module Command.
  Inductive t :=
  | ReadFile (file_name : LString.t)
  | UpdateFile (file_name : LString.t) (content : LString.t)
  | DeleteFile (file_name : LString.t)
  | ListPosts (directory : LString.t)
  | Log (message : LString.t).

  Definition answer (command : t) : Type :=
    match command with
    | ReadFile _ => option LString.t
    | UpdateFile _ _ => bool
    | DeleteFile _ => bool
    | ListPosts _ => option (list Post.Header.t)
    | Log _ => unit
    end.
End Command.

Module C.
  Inductive t (A : Type) : Type :=
  | Ret : forall (x : A), t A
  | Bind : forall {B : Type}, t B -> (B -> t A) -> t A
  | Call : forall (command : Command.t), (Command.answer command -> t A) -> t A.
  Arguments Ret {A} _.
  Arguments Bind {A B} _ _.
  Arguments Call {A} _ _.

  Module Notations.
    Notation "'let!' x ':=' X 'in' Y" :=
      (Bind X (fun x => Y))
      (at level 200, x ident, X at level 100, Y at level 200).

    Notation "'do_let!' X 'in' Y" :=
      (Bind X (fun _ => Y))
      (at level 200, X at level 100, Y at level 200).

    Notation "'call!' answer ':=' command 'in' X" :=
      (Call command (fun answer => X))
      (at level 200, answer ident, command at level 100, X at level 200).

    Notation "'do_call!' command 'in' X" :=
      (Call command (fun _ => X))
      (at level 200, command at level 100, X at level 200).
  End Notations.
End C.
