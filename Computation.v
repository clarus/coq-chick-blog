(** The definition of a computation, used to represent interactive programs. *)
Module C.
  CoInductive t : Type :=
  | Ret : t
  | Let : forall {output : Type} (input : Type), output -> (input -> t) -> t.

  Definition step (c : t) : t :=
    match c with
    | Ret => Ret
    | Let _ input o handler => Let input o handler
    end.

  Lemma step_eq (c : t) : c = step c.
    destruct c; reflexivity.
  Qed.

  Module Notations.
    Notation "'let!' i ':' I ':=' o 'in' X" := (Let I o (fun i => X))
      (at level 200, i ident, I at level 100, o at level 100, X at level 200).

    Notation "'do!' o 'in' X" := (Let unit o (fun _ => X))
      (at level 200, o at level 100, X at level 200).
  End Notations.
End C.
