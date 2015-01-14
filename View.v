Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Http.
Require Import Model.

Import ListNotations.
Local Open Scope char.

Definition header (root : LString.t) : LString.t :=
  LString.s "<!DOCTYPE html>
<html lang=""en"">
  <head>
    <meta charset=""utf-8"">
    <meta name=""viewport"" content=""width=device-width, initial-scale=1"">
    <title>MicroBlog</title>
    <link rel=""stylesheet"" href=""" ++ root ++ LString.s "static/style.min.css"" type=""text/css"" />

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
          <a class=""navbar-brand"" href=""/" ++ root ++ LString.s """>MicroBlog</a>
        </div>
      </div>
      <div class=""article"">
        <div class=""row"">
          <div class=""col-md-1""></div>
            <div class=""col-md-10"">

".

Definition footer : LString.t :=
  LString.s "

          </div>
          <div class=""col-md-1""></div>
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

Definition date (post_header : Post.Header.t) : LString.t :=
  let date := Post.Header.date post_header in
  Date.Print.full_month date ++ LString.s " " ++
  Date.Print.day None date ++ LString.s ", " ++ Date.Print.year 4 None date.

Module Content.
  Definition error : LString.t :=
    LString.s "<p>Error.</p>".

  Definition index (posts : list Post.Header.t) : LString.t :=
    LString.s "<h1>Welcome</h1>
<ul>
  <li>a test to parse the arguments:  <a href=""args?bla=12,13&bli="">/args?bla=12,13&amp;bli=</a></li>
</ul>

<h2>Posts</h2>
<ul>" ++
  LString.join [LString.Char.n] (posts |> List.map (fun post =>
    LString.s "<li><a href=""posts/" ++ Post.Header.url post ++ LString.s "/show"">" ++
    Post.Header.title post ++ LString.s "</a> " ++ date post ++ LString.s "</li>")) ++
  LString.s "</ul>".

  Definition post_show (post : option Post.t) : LString.t :=
    match post with
    | None => LString.s "<p>Post not found.</p>"
    | Some post =>
      let header := Post.header post in
      LString.s "<h1>" ++ Post.Header.title header ++ LString.s " <small><a href=""edit"">edit</a></small></h1>
<p><em>" ++ date header ++ LString.s "</em></p>
" ++ Post.content post
    end.

  Definition post_edit (post : option Post.t) : LString.t :=
    match post with
    | None => LString.s "<p>Post not found.</p>"
    | Some post =>
      let header := Post.header post in
      LString.s "<h1>" ++ Post.Header.title header ++ LString.s "</h1>
<p><em>" ++ date header ++ LString.s "</em></p>
<form action=""update"" method=""GET"">
  <div class=""form-group"">
    <textarea class=""form-control"" name=""content"" rows=""5"">" ++ Post.content post ++ LString.s "</textarea>
  </div>
  <button type=""submit"" class=""btn btn-default"">Submit</button>
</form>"
    end.

  Definition post_update (is_success : bool) : LString.t :=
    LString.s "<p>" ++
    LString.s (if is_success then
      "Post successfully updated."
    else
      "The post could not be updated.") ++
    LString.s "<p>
<p><a href=""show"">Back to the post.</a></p>".

  Definition args (args : Http.Arguments.t) : LString.t :=
    let args := args |> List.map (fun (arg : _ * _) =>
      let (name, values) := arg in
      LString.s "<dt>" ++ name ++ LString.s "</dt><dd>" ++
      LString.join (LString.s ", ") values ++ LString.s "</dd>") in
    LString.s "<h1>Arguments</h1>
<dl class=""dl-horizontal"">
" ++ LString.join [LString.Char.n] args ++
    LString.s "
</dl>".
End Content.

Definition pack (root : LString.t) (content : LString.t) : LString.t :=
  header root ++ content ++ footer.

Definition content (answer : Http.Answer.t) : LString.t :=
  match answer with
  | Http.Answer.Error => Content.error
  | Http.Answer.Static _ content => content
  | Http.Answer.Index posts => pack (LString.s "") @@ Content.index posts
  | Http.Answer.PostShow post => pack (LString.s "../../") @@ Content.post_show post
  | Http.Answer.PostEdit post => pack (LString.s "../../") @@ Content.post_edit post
  | Http.Answer.PostUpdate is_success => pack (LString.s "../../") @@ Content.post_update is_success
  | Http.Answer.Args args => pack (LString.s "") @@ Content.args args
  end.
