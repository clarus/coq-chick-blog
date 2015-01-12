Require Import ListString.All.
Require Import Computation.
Require Extraction.

Import C.Notations.

Definition hello_world : C.t :=
  do! Command.Log @ LString.s "Hello world!" in
  C.Ret.

Definition extracted_hello_world : unit :=
  Extraction.eval hello_world.

Extraction "extraction/hello_world" extracted_hello_world.
