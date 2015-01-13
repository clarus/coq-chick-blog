Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Http.

Import ListNotations.
Local Open Scope char.

Definition header : LString.t := LString.s
"<!DOCTYPE html>
<html lang=""en"">
  <head>
    <meta charset=""utf-8"">
    <meta name=""viewport"" content=""width=device-width, initial-scale=1"">
    <title>MicroBlog</title>
    <link rel=""stylesheet"" href=""static/style.min.css"" type=""text/css"" />

    <!-- HTML5 Shim and Respond.js IE8 support of HTML5 elements and media queries -->
    <!-- WARNING: Respond.js doesn't work if you view the page via file:// -->
    <!--[if lt IE 9]>
      <script src=""https://oss.maxcdn.com/html5shiv/3.7.2/html5shiv.min.js""></script>
      <script src=""https://oss.maxcdn.com/respond/1.4.2/respond.min.js""></script>
    <![endif]-->
  </head>
  <body>
    <div class=""container-fluid"">
      <div class=""navbar navbar-default"" role=""navigation"">
        <div class=""navbar-header"">
          <a class=""navbar-brand"" href=""."">MicroBlog</a>
        </div>
      </div>
      <div class=""article"">
        <div class=""row"">
          <div class=""col-md-12"">

".

Definition footer : LString.t := LString.s
"

          </div>
        </div>
      </div>
      <hr/>
      <div class=""footer"">
        <p class=""text-center"">
          <small>Sources are on <a href=""https://github.com/clarus/coq-micro-blog"">GitHub</a>. © Guillaume Claret</small>
        </p>
      </div>
    </div>
  </body>
</html>
".

Definition mime_type (answer : Http.Answer.t) : LString.t :=
  match answer with
  | Http.Answer.Static mime_type _ => mime_type
  | _ => LString.s "text/html; charset=utf-8"
  end.

Module Content.
  Definition error : LString.t :=
    LString.s "<h1>Error</h1>".

  Definition index : LString.t :=
    LString.s "<h1>Welcome</h1>
<ul>
  <li>the list of users: <a href=""users"">/users</a></li>
  <li>a test to parse the arguments:  <a href=""args?bla=12,13&bli="">/args?bla=12,13&amp;bli=</a></li>
</ul>".

  Definition users : LString.t :=
    LString.s "<h1>Users</h1>
<p>The list of users.</p>".

  Definition args (args : list (LString.t * list LString.t)) : LString.t :=
    let args := args |> List.map (fun (arg : _ * _) =>
      let (name, values) := arg in
      LString.s "<dt>" ++ name ++ LString.s "</dt><dd>" ++
      LString.join (LString.s ", ") values ++
      LString.s "</dd>") in
    LString.s "<h1>Arguments</h1>
<dl class=""dl-horizontal"">
" ++ LString.join [LString.Char.n] args ++
    LString.s "
</dl>".
End Content.

Definition pack (content : LString.t) : LString.t :=
  header ++ content ++ footer.

Definition content (answer : Http.Answer.t) : LString.t :=
  match answer with
  | Http.Answer.Error => pack Content.error
  | Http.Answer.Static _ content => content
  | Http.Answer.Index => pack Content.index
  | Http.Answer.Users => pack Content.users
  | Http.Answer.Args args => pack @@ Content.args args
  end.
