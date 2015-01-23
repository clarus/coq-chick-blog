(** Responses from the server. *)
Require Import ListString.All.
Require Http.
Require Import Model.

(** Sum type of the responses. *)
Inductive t :=
(** Errors. *)
| NotFound | WrongArguments | Forbidden
(** Static content from the `static/` folder. *)
| Static (mime_type : LString.t) (content : LString.t)
(** Confirm that you are logged in or out. *)
| Login | Logout
(** The index page. *)
| Index (is_logged : bool) (posts : list Post.Header.t)
(** The page of a post. *)
| PostShow (is_logged : bool) (url : LString.t) (post : option Post.t)
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

(** Raw responses after pretty-printing in `Render.v`. The return code is always
    200 (OK). *)
Module Raw.
  Record t := New {
    mime_type : LString.t;
    cookies : Http.Cookies.t;
    content : LString.t }.
End Raw.
