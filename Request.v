(** Requests from the client. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Moment.All.
Require Http.

Import ListNotations.
Local Open Scope string.

(** Raw requests as given by the CoHTTP library. *)
Module Raw.
  Record t := New {
    path : list LString.t;
    args : Http.Arguments.t;
    cookies : Http.Cookies.t }.
End Raw.

(** Parsed path of a request, including the url with its arguments. *)
Module Path.
  Inductive t :=
  | NotFound
  | WrongArguments
  | Static (path : list LString.t)
  | Index
  | Login | Logout
  | PostAdd
  | PostDoAdd (title : LString.t) (date : Moment.Date.t)
  | PostShow (post_url : LString.t)
  | PostEdit (post_url : LString.t)
  | PostDoEdit (post_url : LString.t) (content : LString.t)
  | PostDoDelete (post_url : LString.t).

  (** Try to parse the arguments of a "/do_add" request. *)
  Definition parse_do_add_args (args : Http.Arguments.t)
    : option (LString.t * Moment.Date.t) :=
    let title := Http.Arguments.find args @@ LString.s "title" in
    let year := Http.Arguments.find args @@ LString.s "year" in
    let month := Http.Arguments.find args @@ LString.s "month" in
    let day := Http.Arguments.find args @@ LString.s "day" in
    match (title, year, month, day) with
    | (Some [title], Some [year], Some [month], Some [day]) =>
      let year := Moment.Date.Parse.zero_padded_year 4 year in
      let month := Moment.Date.Parse.zero_padded_month month in
      let day := Moment.Date.Parse.zero_padded_day day in
      match (year, month, day) with
      | (Some (year, []), Some (month, []), Some (day, [])) =>
        let date := Moment.Date.New year month day in
        Some (title, date)
      | _ => None
      end
    | _ => None
    end.

  (** Parse a request URL with its arguments. This function is a kind of
      router. *)
  Definition parse (path : list LString.t) (args : Http.Arguments.t) : t :=
    match List.map LString.to_string path with
    | "static" :: path => Static (List.map LString.s path)
    | [] => Index
    | ["login"] => Login
    | ["logout"] => Logout
    | ["posts"; command] =>
      match command with
      | "add" => PostAdd
      | "do_add" =>
        match parse_do_add_args args with
        | Some (title, date) => PostDoAdd title date
        | None => WrongArguments
        end
      | _ => NotFound
      end
    | ["posts"; command; post_url] =>
      let post_url := LString.s post_url in
      match command with
      | "show" => PostShow post_url
      | "edit" => PostEdit post_url
      | "do_edit" =>
        match Http.Arguments.find args @@ LString.s "content" with
        | Some [content] => PostDoEdit post_url content
        | _ => WrongArguments
        end
      | "do_delete" => PostDoDelete post_url
      | _ => NotFound
      end
    | _ => NotFound
    end.
End Path.

(** Hight-level definition of cookies. *)
Module Cookies.
  (** Cookies can represent two states: logged in or logged out. *)
  Inductive t :=
  | LoggedIn
  | LoggedOut.

  (** Test if the cookies mean that we are logged in. *)
  Definition is_logged (cookies : t) : bool :=
    match cookies with
    | LoggedIn => true
    | LoggedOut => false
    end.

  (** Parse raw cookies given by the client. *)
  Definition parse (cookies : Http.Cookies.t) : t :=
    match Http.Cookies.find cookies @@ LString.s "is_logged" with
    | Some is_logged =>
      if LString.eqb is_logged @@ LString.s "true" then
        LoggedIn
      else
        LoggedOut
    | None => LoggedOut
    end.
End Cookies.

(** Parse the path and the cookies. *)
Definition parse (request : Raw.t) : Path.t * Cookies.t := (
  Path.parse (Raw.path request) (Raw.args request),
  Cookies.parse (Raw.cookies request)).
