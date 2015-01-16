(** Specifications. *)
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

(** A run is an execution of the program with explicit answers for the
    system calls. *)
Module Run.
  (** We define a run by induction on the structure of a computation. *)
  Inductive t {A : Type} : C.t A -> A -> Type :=
  | Ret : forall (x : A), t (C.Ret x) x
  | Call : forall (command : Command.t) (answer : Command.answer command)
    {handler : Command.answer command -> C.t A} {x : A}, t (handler answer) x ->
    t (C.Call command handler) x.

  (** Extract the answer and the run of the handler from a run on a call. *)
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

(** Scenarios are parametrized runs of computations. Type-checking scenarios
    shows that a computation is behaving as expected. Scenarios are more generic
    than unit tests because some variables can be universally quantified. *)
Module SimpleScenarios.
  Import Run.

  (** The index page when the list of posts is available. *)
  Definition index_ok (cookies : Request.Cookies.t)
    (post_headers : list Post.Header.t)
    : Run.t (Main.server Request.Path.Index cookies) @@ Answer.Public
      (Request.Cookies.is_logged @@ cookies)
      (Answer.Public.Index post_headers).
    (* We ask to list the available posts. *)
    apply (Call (Command.ListPosts _ ) (Some post_headers)).
    (* The program terminates. *)
    apply Ret.
  Defined.

  (** The index page when the list of posts is not available. *)
  Definition index_wrong (cookies : Request.Cookies.t)
    : Run.t (Main.server Request.Path.Index cookies) @@ Answer.Public
      (Request.Cookies.is_logged @@ cookies)
      (Answer.Public.Index []).
    (* We ask to list the available posts. *)
    apply (Call (Command.ListPosts _ ) None).
    (* We print an error message. *)
    apply (Call (Command.Log _ ) tt).
    (* The program terminates. *)
    apply Ret.
  Defined.

  (** It is not possible to add a post if not logged in. *)
  Definition if_not_logged_add_is_forbidden (title : LString.t)
    (date : Moment.Date.t)
    : Run.t
      (Main.server (Request.Path.PostDoAdd title date) Request.Cookies.LoggedOut)
      Answer.Forbidden.
    (* The program does no system calls. *)
    apply Ret.
  Defined.
End SimpleScenarios.

(** Complex scenarios are scenarios over a list of successive requests. *)
Module ComplexScenarios.
  Import Run.

  (** The run of one request. *)
  Module RequestRun.
    Record t := New {
      path : Request.Path.t;
      cookies : Request.Cookies.t;
      answer : Answer.t;
      run : Run.t (Main.server path cookies) answer }.
  End RequestRun.

  (** A list of successive runs of requests. *)
  Module RequestsRun.
    Definition t := list RequestRun.t.
  End RequestsRun.

  (** Run the `post_header` helper on the `post_header` URL for a list of posts
      in the file system being `post_header :: post_headers`, given a run of
      the continuation. *)
  Definition helpers_post_header {A : Type} {k : option Post.Header.t -> C.t A}
    (post_header : Post.Header.t) (post_headers : list Post.Header.t) (x : A)
    (run_k : Run.t (k (Some post_header)) x)
    : Run.t (Main.Helpers.post_header (Post.Header.url post_header) k) x.
    unfold Main.Helpers.post_header.
    apply (Call (Command.ListPosts _) (Some (post_header :: post_headers))).
    unfold apply; simpl.
    rewrite LString.eqb_same_is_eq.
    exact run_k.
  Defined.

  (** Run the `post` helper on the `post_header` URL for a list of posts in the
      file system being `post_header :: post_headers`, given a run of
      the continuation. *)
  Definition helpers_post {A : Type} {k : option Post.t -> C.t A}
    (post_header : Post.Header.t) (post_headers : list Post.Header.t)
    (content : LString.t) (x : A)
    (run_k : Run.t (k (Some (Post.New post_header content))) x)
    : Run.t (Main.Helpers.post (Post.Header.url post_header) k) x.
    apply (helpers_post_header post_header post_headers).
    apply (Call
      (Command.ReadFile (_ ++ Post.Header.file_name post_header))
      (Some content)).
    exact run_k.
  Defined.

  (** Add, edit and read a post as an authenticated user. We check that we find
      back the post content we edited. *)
  Definition write_and_read (title : LString.t) (date : Moment.Date.t)
    (content : LString.t) (post_headers : list Post.Header.t) : RequestsRun.t.
    refine (
      let url := Model.Post.Header.to_url title in
      let file_name := Moment.Date.Print.date date ++ LString.s " " ++ title ++
        LString.s ".html" in
      let post_header := Post.Header.New title date url file_name in
      let post := Post.New post_header content in _).
    (* /do_add *)
    apply cons.
    apply (RequestRun.New
      (Request.Path.PostDoAdd title date) Request.Cookies.LoggedIn
      (Answer.Private (Answer.Private.PostDoAdd true))).
    apply (Call
      (Command.UpdateFile (Main.posts_directory ++ file_name) (LString.s ""))
      true).
    apply Ret.
    (* /posts/do_edit *)
    apply cons.
    apply (RequestRun.New
      (Request.Path.PostDoEdit url content) Request.Cookies.LoggedIn
      (Answer.Private (Answer.Private.PostDoEdit url true))).
    apply (helpers_post_header post_header post_headers).
    apply (Call
      (Command.UpdateFile (Main.posts_directory ++ file_name) content)
      true).
    apply Ret.
    (* /posts/show *)
    apply cons.
    apply (RequestRun.New
      (Request.Path.PostShow url) Request.Cookies.LoggedIn
      (Answer.Public true (Answer.Public.PostShow url (Some post)))).
    apply (helpers_post post_header post_headers content).
    apply Ret.
    (* end *)
    apply nil.
  Defined.
End ComplexScenarios.

(** We check that only public pages are accessible without login. *)
Module PrivateAnswers.
  (** Test if an answer has a private content. *)
  Definition is_private (answer : Answer.t) : bool :=
    match answer with
    | Answer.Private _ => true
    | _ => false
    end.

  (** We cannot access private pages without the logged-in cookie. We check that
      there is no runs with a logged out cookie to a private page. We reason by
      disjunction over the path. *)
  Lemma if_not_logged_no_private_pages (path : Request.Path.t)
    (answer : Answer.t)
    (run : Run.t (Main.server path Request.Cookies.LoggedOut) answer)
    : is_private answer = false.
    destruct path; try (inversion run; reflexivity);
      unfold Main.server in run.
    - unfold Main.Controller.static in run.
      destruct (Run.inversion_call run) as [content run1].
      destruct content; inversion run1; reflexivity.
    - unfold Main.Controller.index in run.
      destruct (Run.inversion_call run) as [post_headers run1].
      destruct post_headers.
      + inversion run1; reflexivity.
      + destruct (Run.inversion_call run1) as [tt run2].
        inversion run2; reflexivity.
    - destruct (Run.inversion_call run) as [post_headers run1].
      destruct post_headers as [post_headers |].
      + simpl in run1.
        destruct (find _ @@ _).
        * destruct (Run.inversion_call run1) as [content run2].
          inversion run2; reflexivity.
        * inversion run1; reflexivity.
      + inversion run1; reflexivity.
  Qed.
End PrivateAnswers.

(** We check that an unauthenticated user cannot modify the file system. *)
Module ReadOnly.
  (** Test if a system call does not modify the file system. *)
  Definition is_read (command : Command.t) : bool :=
    match command with
    | Command.ReadFile _ | Command.ListPosts _ | Command.Log _ => true
    | _ => false
    end.

  (** The read-only predicate is defined inductively over a computation. *)
  Inductive t {A : Type} : C.t A -> Prop :=
  | Ret : forall {x : A}, t (C.Ret x)
  | Call : forall (command : Command.t)
    (handler : Command.answer command -> C.t A),
    is_read command = true ->
    (forall (answer : Command.answer command), t (handler answer)) ->
    t (C.Call command handler).

  (** We show that we cannot modify the file system if not logged by disjunction
      over the path. *)
  Lemma if_not_logged_no_writes (path : Request.Path.t)
    : t (Main.server path Request.Cookies.LoggedOut).
    destruct path; try apply Ret; unfold Main.server.
    - unfold Main.Controller.static.
      apply Call; try reflexivity.
      intro answer; destruct answer; apply Ret.
    - unfold Main.Controller.index.
      apply Call; try reflexivity.
      intro answer; destruct answer; try apply Ret.
      apply Call; try reflexivity.
      intro; apply Ret.
    - unfold Main.Controller.post_show.
      apply Call; try reflexivity.
      intro answer; destruct answer; try apply Ret.
      simpl.
      destruct (find _ @@ _); try apply Ret.
      apply Call; try reflexivity.
      intro answer; destruct answer; apply Ret.
  Qed.
End ReadOnly.
