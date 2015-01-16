(** Answers from the server. *)
Require Import ListString.All.
Require Http.
Require Import Model.

(** Public pages (do not require to login). *)
Module Public.
  Inductive t :=
  | Index (posts : list Post.Header.t)
  | PostShow (url : LString.t) (post : option Post.t).
End Public.

(** Private pages (require to login). *)
Module Private.
  Inductive t :=
  (** Form to add a post. *)
  | PostAdd
  (** Confirm that a post is added. *)
  | PostDoAdd (is_success : bool)
  (** Form to edit a post. *)
  | PostEdit (url : LString.t) (post : option Post.t)
  (** Confirm that a post is edited. *)
  | PostDoEdit (url : LString.t) (is_success : bool)
  (** Confirm that a post is deleted. *)
  | PostDoDelete (is_success : bool).
End Private.

(** Sum type of the answers. *)
Inductive t :=
(** Errors. *)
| NotFound | WrongArguments | Forbidden
(** Static content from the `static/` folder. *)
| Static (mime_type : LString.t) (content : LString.t)
(** Confirm that you are logged in or out. *)
| Login | Logout
(** Public pages. *)
| Public (is_logged : bool) (page : Public.t)
(** Private pages. *)
| Private (page : Private.t).

(** Raw answers after pretty-printing in `Render.v`. The return code is always
    200 (OK). *)
Module Raw.
  Record t := New {
    mime_type : LString.t;
    cookies : Http.Cookies.t;
    content : LString.t }.
End Raw.
