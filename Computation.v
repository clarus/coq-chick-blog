(** The definition of computations, used to represent interactive programs. *)
Require Import ListString.All.
Require Import Model.

Local Open Scope type.

Module Command.
  Inductive t :=
  | ReadFile (file_name : LString.t)
  | ListPosts (directory : LString.t)
  | Log (message : LString.t).

  Definition answer (command : t) : Type :=
    match command with
    | ReadFile _ => option LString.t
    | ListPosts _ => option (list Post.Header.t)
    | Log _ => unit
    end.
End Command.

Module C.
  Inductive t (A : Type) : Type :=
  | Ret : forall (x : A), t A
  | Let : forall (command : Command.t), (Command.answer command -> t A) -> t A.
  Arguments Ret {A} _.
  Arguments Let {A} _ _.

  Module Notations.
    Notation "'let!' answer ':=' command 'in' X" :=
      (Let command (fun answer => X))
      (at level 200, answer ident, command at level 100, X at level 200).

    Notation "'do!' command 'in' X" :=
      (Let command (fun _ => X))
      (at level 200, command at level 100, X at level 200).
  End Notations.
End C.
