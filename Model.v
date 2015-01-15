Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.Ascii.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Moment.All.

Import ListNotations.
Local Open Scope char.

Module Post.
  Module Header.
    Record t := New {
      title : LString.t;
      date : Moment.Date.t;
      url : LString.t;
      file_name : LString.t }.

    Fixpoint to_url (title : LString.t) : LString.t :=
      match title with
      | [] => []
      | c :: title =>
        let n := Ascii.N_of_ascii c in
        let n_a := Ascii.N_of_ascii "a" in
        let n_z := Ascii.N_of_ascii "z" in
        let n_A := Ascii.N_of_ascii "A" in
        let n_Z := Ascii.N_of_ascii "Z" in
        let n_0 := Ascii.N_of_ascii "0" in
        let n_9 := Ascii.N_of_ascii "9" in
        if (N.leb n_a n && N.leb n n_z) || (N.leb n_A n && N.leb n n_Z) ||
          (N.leb n_0 n && N.leb n n_9) then
          LString.Char.down_case c :: to_url title 
        else
          "-" :: to_url title
      end.

    (** Eat one dash at the beginning of the string. *)
    Definition eat_dash (s : LString.t) : option LString.t :=
      match s with
      | "-" :: s => Some s
      | _ => None
      end.

    (** Eat zero, one or many spaces at the beginning of the string. *)
    Fixpoint eat_spaces (s : LString.t) : LString.t :=
      match s with
      | " " :: s => eat_spaces s
      | _ => s
      end.

    Definition of_file_name (file_name : LString.t) : option t :=
      Option.bind (Date.Parse.zero_padded_year 4 file_name) (fun x =>
      let (year, file_name') := x in
      Option.bind (eat_dash file_name') (fun file_name' =>
      Option.bind (Date.Parse.zero_padded_month file_name') (fun x =>
      let (month, file_name') := x in
      Option.bind (eat_dash file_name') (fun file_name' =>
      Option.bind (Date.Parse.zero_padded_day file_name') (fun x =>
      let (day, file_name') := x in
      let date := Date.New year month day in
      let extension := List.last (LString.split file_name' ".") (LString.s "") in
      if LString.eqb extension @@ LString.s "html" then
        let title := List.removelast (LString.split file_name' ".")
          |> LString.join []
          |> eat_spaces in
        Some (New title date (to_url title) file_name)
      else
        None))))).
  End Header.

  Record t := New {
    header : Header.t;
    content : LString.t }.
End Post.
