Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ListString.All.

Import ListNotations.
Local Open Scope string.

Module User.
  Record t := New {
    password : LString.t;
    email : LString.t }.
End User.

Module Users.
  Definition t := list (LString.t * User.t).

  Fixpoint add (users : t) (login : LString.t) (user : User.t) : t :=
    match users with
    | [] => [(login, user)]
    | (login', user') :: users =>
      if LString.eqb login login' then
        (login, user) :: users
      else
        (login', user') :: add users login user
    end.
End Users.
