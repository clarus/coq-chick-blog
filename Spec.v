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

  Definition inversion_call : forall {A : Type} {command : Command.t}
    {handler : Command.answer command -> C.t A} {x : A}
    (run : t (C.Call command handler) x),
    {answer : Command.answer command & t (handler answer) x}.
    intros.
    inversion_clear run.
    exists answer.
    exact X.
  Defined.
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

(** The index page when the list of posts is not available. *)
Definition index_wrong (cookies : Request.Cookies.t)
  : Run.t (Main.server Request.Path.Index cookies) @@ Answer.Public
    (Request.Cookies.is_logged @@ cookies)
    (Answer.Public.Index []).
  apply (Call (Command.ListPosts _ ) None).
  apply (Call (Command.Log _ ) tt).
  apply Ret.
Defined.

(** Test if an answer has a private content. *)
Definition is_private (answer : Answer.t) : bool :=
  match answer with
  | Answer.Private _ => true
  | _ => false
  end.

(** We cannot access private pages without the logged-in cookie. *)
Definition if_not_logged_no_private_pages (path : Request.Path.t)
  (answer : Answer.t)
  (run : Run.t (Main.server path Request.Cookies.LoggedOut) answer)
  : is_private answer = false.
  destruct path; try (inversion run; reflexivity);
    unfold Main.server in run; simpl in run.
  - unfold Main.Controller.static in run.
    destruct (inversion_call run) as [content run1].
    destruct content; inversion run1; reflexivity.
  - unfold Main.Controller.index in run.
    destruct (inversion_call run) as [post_headers run1].
    destruct post_headers.
    + inversion run1; reflexivity.
    + destruct (inversion_call run1) as [tt run2].
      inversion run2; reflexivity.
  - destruct (inversion_call run) as [post_headers run1].
    destruct post_headers as [post_headers |].
    + simpl in run1.
      destruct (find _ @@ _).
      * destruct (inversion_call run1) as [content run2].
        inversion run2; reflexivity.
      * inversion run1; reflexivity.
    + inversion run1; reflexivity.
Defined.

Module ReadOnly.
  Definition is_read (command : Command.t) : bool :=
    match command with
    | Command.ReadFile _ | Command.ListPosts _ | Command.Log _ => true
    | _ => false
    end.

  Inductive t {A : Type} : forall {x : C.t A} {v : A}, Run.t x v -> Prop :=
  | Ret : forall (x : A), t (Run.Ret x)
  | Call : forall (command : Command.t) (answer : Command.answer command)
    (handler : Command.answer command -> C.t A) (v : A)
    (run : Run.t (handler answer) v), is_read command = true -> t run ->
    t (Run.Call command answer run).
End ReadOnly.
