Require Import Coq.Lists.List.
Require Import FunctionNinjas.All.
Require Import ListString.All.

Import ListNotations.

Module LStringMap.
  Definition t (A : Type) := list (LString.t * A).

  Fixpoint find {A : Type} (map : t A) (key : LString.t) : option A :=
    match map with
    | [] => None
    | (key', val) :: map =>
      if LString.eqb key key' then
        Some val
      else
        find map key
    end.
End LStringMap.

Module Arguments.
  Definition t := LStringMap.t (list LString.t).

  Definition find (args : t) (key : LString.t) : option (list LString.t) :=
    LStringMap.find args key.
End Arguments.

Module Cookies.
  Definition t := LStringMap.t LString.t.

  Fixpoint find (cookies : t) (key : LString.t) : option LString.t :=
    LStringMap.find cookies key.

  Definition is_logged (cookies : t) : bool :=
    match find cookies @@ LString.s "is_logged" with
    | Some is_logged => LString.eqb is_logged @@ LString.s "true"
    | None => false
    end.
End Cookies.
