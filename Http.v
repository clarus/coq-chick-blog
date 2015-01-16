(** Useful types for HTTP interactions. *)
Require Import Coq.Lists.List.
Require Import FunctionNinjas.All.
Require Import ListString.All.

Import ListNotations.

(** A map from strings to values. *)
Module LStringMap.
  (** Naive implementation of a map with an association list. *)
  Definition t (A : Type) := list (LString.t * A).

  (** Try to find the value of a key. *)
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

(** The arguments as given at the end of an url. For example:
    example.com/index.html?arg1=v11,v12&arg2=v2 *)
Module Arguments.
  (** A map of keys to argument lists (the most common case is a list of one
      value). *)
  Definition t := LStringMap.t (list LString.t).

  (** Try to find the values of an argument. *)
  Definition find (args : t) (key : LString.t) : option (list LString.t) :=
    LStringMap.find args key.
End Arguments.

(** Cookies, given by the client or set by the server. *)
Module Cookies.
  (** A cookie is a key and a value. *)
  Definition t := LStringMap.t LString.t.

  (** Try to find the value of a cookie. *)
  Fixpoint find (cookies : t) (key : LString.t) : option LString.t :=
    LStringMap.find cookies key.
End Cookies.
