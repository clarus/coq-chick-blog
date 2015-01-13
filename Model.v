Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ListString.All.

Import ListNotations.

Module Post.
  Module Header.
    Record t := New {
      title : LString.t;
      date : LString.t;
      file_name : LString.t }.
  End Header.

  Record t := New {
    header : Header.t;
    body : LString.t }.
End Post.
