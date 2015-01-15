Require Http.

Inductive t :=
| Get (path : list LString.t) (args : Http.Arguments.t) (cookies : Http.Cookies.t).
