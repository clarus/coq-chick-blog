Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Computation.
Require Http.
Require Main.
Require Import Model.
Require Request.

Import ListNotations.
Local Open Scope char.

Module Run.
  Inductive t {A : Type} : C.t A -> A -> Type :=
  | Ret : forall (x : A), t (C.Ret x) x
  | Call : forall (command : Command.t) (answer : Command.answer command)
    {handler : Command.answer command -> C.t A} {x : A}, t (handler answer) x ->
    t (C.Call command handler) x.
End Run.

Import Run.

(** The index page when the list of posts is available. *)
Definition index (cookies : Request.Cookies.t)
  (post_headers : list Post.Header.t)
  : Run.t (Main.server Request.Path.Index cookies) @@ Answer.Public
    (Request.Cookies.is_logged @@ cookies)
    (Answer.Public.Index post_headers).
  apply (Call (Command.ListPosts _ ) (Some post_headers)).
  apply Ret.
Defined.

(*(** The index page when the list of posts is available. *)
Definition index (cookies : Request.Cookies.t)
  (post_headers : list Post.Header.t)
  : Run.t (Main.server Request.Path.Index cookies) _ :=
  Call (Command.ListPosts _ ) (Some post_headers) @@
  Ret (Answer.Public
    (Request.Cookies.is_logged @@ cookies)
    (Answer.Public.Index post_headers)).

(** The index page when the list of posts is not available. *)
Definition index_wrong (cookies : Request.Cookies.t)
  : Run.t (Main.server Request.Path.Index cookies) _.
  apply (Call (Command.ListPosts _ ) None).
  apply (Call (Command.Log _ ) tt).
  exact (Ret (Answer.Public
    (Request.Cookies.is_logged @@ cookies)
    (Answer.Public.Index []))).
Defined.

(** Test if an answer has a private content. *)
Definition is_private (answer : Answer.t) : bool :=
  match answer with
  | Answer.Private _ => true
  | _ => false
  end.

Definition if_not_logged_no_private_pages (path : Request.Path.t)
  : forall (run : Run.t (Main.server path Request.Cookies.LoggedOut)),
    is_private (eval run) = false.
  destruct path.
  unfold Main.server; simpl.
  unfold Main.Controller.not_found.
  intro run.
  destruct run.
  - simpl.
  inversion run.
Defined.
*)