Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.

Import ListNotations.

Definition t (A : Type) : Type := list (N * A).

Definition empty {A : Type} : t A :=
  [].

Definition add {A : Type} (m : t A) (id : N) (x : A) : t A.
Admitted.

Definition find {A : Type} (m : t A) (id : N) : option A.
Admitted.

Definition remove {A : Type} (m : t A) (id : N) : t A.
Admitted.
