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
    <title>Checking concurrent programs with symbolic simulations</title>
    <link rel=""stylesheet"" href=""static/style.min.css"" type=""text/css"" />
    <link rel=""icon"" type=""image/png"" href=""static/favicon.png"" />
    <link rel=""alternate"" type=""application/rss+xml"" href=""rss.xml"" />

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
          <a class=""navbar-brand"" href=""."">Coq blog - Guillaume Claret</a>
        </div>
      </div>
      <div class=""article"">


<div class=""row"">
  <div class=""col-md-12"">".

Definition footer : LString.t := LString.s
"          </div>
        </div>
      </div>
      <hr/>
      <div class=""footer"">
        <p class=""text-center"">
          <small><a href=""rss.xml"">RSS feed</a></small>
        </p>
        <p class=""text-center"">
          <small>Sources are on <a href=""https://github.com/clarus/coq-blog"">GitHub</a>. © Guillaume Claret</small>
        </p>
      </div>
    </div>
  </body>
</html>".

Definition mime_type (answer : Http.Answer.t) : LString.t :=
  match answer with
  | Http.Answer.Static mime_type _ => mime_type
  | _ => LString.s "text/html; charset=utf-8"
  end.

Definition content (answer : Http.Answer.t) : LString.t :=
  header ++
  match answer with
  | Http.Answer.Error => LString.s "Error"
  | Http.Answer.Static _ content => content
  | Http.Answer.Index => LString.s "Welcome to the index page!"
  | Http.Answer.Users => LString.s "This will be the list of users."
  | Http.Answer.Args args =>
    let args := args |> List.map (fun (arg : _ * _) =>
      let (name, values) := arg in
      name ++ LString.s ": " ++ LString.join (LString.s ", ") values) in
    LString.join (LString.s "<br/>" ++ [LString.Char.n]) args
  end ++
  footer.
