Require Http.

Module Raw.
  Record t := New {
    path : list LString.t;
    args : Http.Arguments.t;
    cookies : Http.Cookies.t }.
End Raw.

Definition t := Raw.t.
