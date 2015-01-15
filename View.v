Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Http.
Require Import Model.

Import ListNotations.
Local Open Scope char.

Definition header (root : LString.t) (is_logged : option bool) : LString.t :=
  LString.s "<!DOCTYPE html>
<html lang=""en"">
  <head>
    <meta charset=""utf-8"">
    <meta name=""viewport"" content=""width=device-width, initial-scale=1"">
    <title>ChickBlog</title>
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
          <a class=""navbar-brand"" href=""/" ++ root ++ LString.s """>ChickBlog</a>
        </div>" ++
  match is_logged with
  | None => LString.s ""
  | Some is_logged => LString.s "
        <div class=""collapse navbar-collapse"" id=""bs-example-navbar-collapse-1"">
          <ul class=""nav navbar-nav navbar-right"">
            <li><a href=""" ++ root ++
  LString.s (if is_logged then "logout" else "login") ++ LString.s """>" ++
  LString.s (if is_logged then "Logout" else "Login") ++
  LString.s "</a></li>
          </ul>
        </div>"
  end ++ LString.s "
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
          <small>Sources are on <a href=""https://github.com/clarus/coq-chick-blog"">GitHub</a>. © Guillaume Claret</small>
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

Definition cookies (answer : Http.Answer.t) : Http.Cookies.t :=
  match answer with
  | Http.Answer.Login => [(LString.s "is_logged", LString.s "true")]
  | Http.Answer.Logout => [(LString.s "is_logged", LString.s "false")]
  | _ => []
  end.

Definition date (post_header : Post.Header.t) : LString.t :=
  let date := Post.Header.date post_header in
  Date.Print.full_month date ++ LString.s " " ++
  Date.Print.day None date ++ LString.s ", " ++ Date.Print.year 4 None date.

Module Content.
  Definition login : LString.t :=
    LString.s "<p>You are logged in.</p>".

  Definition logout : LString.t :=
    LString.s "<p>You are logged out.</p>".

  Definition index (is_logged : bool) (posts : list Post.Header.t) : LString.t :=
    LString.s "<h1>Welcome</h1>
<p>This is a blog written and proven in <a href=""https://coq.inria.fr/"">Coq</a>. The sources are on <a href=""https://github.com/clarus/coq-chick-blog"">GitHub</a>.</p>

<h2>Posts" ++
  LString.s (if is_logged then " <small><a href=""/posts/add"">add</a></small>" else "") ++
  LString.s "</h2>
<ul>" ++
  LString.join [LString.Char.n] (posts |> List.map (fun post =>
    LString.s "<li><a href=""/posts/show/" ++ Post.Header.url post ++ LString.s """>" ++
    Post.Header.title post ++ LString.s "</a> " ++ date post ++ LString.s "</li>")) ++
  LString.s "</ul>".

  Definition post_show (is_logged : bool) (url : LString.t) (post : option Post.t) : LString.t :=
    match post with
    | None => LString.s "<p>Post not found.</p>"
    | Some post =>
      let header := Post.header post in
      LString.s "<h1>" ++ Post.Header.title header ++
      (if is_logged then
        LString.s "
<small><a href=""/posts/edit/" ++ url ++ LString.s """>edit</a></small>
<small><a href=""/posts/do_delete/" ++ url ++ LString.s """>delete</a></small>"
      else
        LString.s "") ++
      LString.s "</h1>
<p><em>" ++ date header ++ LString.s "</em></p>
" ++ Post.content post
    end.

  Definition post_add : LString.t :=
    LString.s "<h1>Add post</h1>
<form method=""GET"" action=""/posts/do_add"">
  <div class=""form-group"">
    <label for=""title"">Title</label>
    <input type=""text"" class=""form-control"" id=""title"" name=""title"" placeholder=""Enter a title"">
  </div>
  <div class=""form-group"">
    <label for=""year"">Year</label>
    <select class=""form-control"" id=""year"" name=""year"">
      <option>2015</option>
      <option>2016</option>
      <option>2017</option>
      <option>2018</option>
      <option>2019</option>
      <option>2020</option>
    </select>
    <label for=""month"">Month</label>
    <select class=""form-control"" id=""month"" name=""month"">
      <option>01</option>
      <option>02</option>
      <option>03</option>
      <option>04</option>
      <option>05</option>
      <option>06</option>
      <option>07</option>
      <option>08</option>
      <option>09</option>
      <option>10</option>
      <option>11</option>
      <option>12</option>
    </select>
    <label for=""day"">Day</label>
    <select class=""form-control"" id=""day"" name=""day"">
      <option>01</option>
      <option>02</option>
      <option>03</option>
      <option>04</option>
      <option>05</option>
      <option>06</option>
      <option>07</option>
      <option>08</option>
      <option>09</option>
      <option>10</option>
      <option>11</option>
      <option>12</option>
      <option>13</option>
      <option>14</option>
      <option>15</option>
      <option>16</option>
      <option>17</option>
      <option>18</option>
      <option>19</option>
      <option>20</option>
      <option>21</option>
      <option>22</option>
      <option>23</option>
      <option>24</option>
      <option>25</option>
      <option>26</option>
      <option>27</option>
      <option>28</option>
      <option>29</option>
      <option>30</option>
      <option>31</option>
    </select>
  </div>
  <button type=""submit"" class=""btn btn-default"">Submit</button>
</form>".

  Definition post_do_add (is_success : bool) : LString.t :=
    if is_success then
      LString.s "<p>Post successfully added.</p>"
    else
      LString.s "<p>The post could not be added.</p>".

  Definition post_edit (url : LString.t) (post : option Post.t) : LString.t :=
    match post with
    | None => LString.s "<p>Post not found.</p>"
    | Some post =>
      let header := Post.header post in
      LString.s "<h1>" ++ Post.Header.title header ++ LString.s "</h1>
<p><em>" ++ date header ++ LString.s "</em></p>
<form action=""/posts/do_edit/" ++ url ++ LString.s """ method=""GET"">
  <div class=""form-group"">
    <textarea class=""form-control"" name=""content"" rows=""5"">" ++ Post.content post ++ LString.s "</textarea>
  </div>
  <button type=""submit"" class=""btn btn-default"">Submit</button>
</form>"
    end.

  Definition post_do_edit (url : LString.t) (is_success : bool) : LString.t :=
    LString.s "<p>" ++
    LString.s (if is_success then
      "Post successfully updated."
    else
      "The post could not be updated.") ++
    LString.s "<p>
<p><a href=""/posts/show/" ++ url ++ LString.s """>Back to the post.</a></p>".

  Definition post_do_delete (is_success : bool) : LString.t :=
    LString.s "<p>" ++
    LString.s (if is_success then
      "Post successfully removed."
    else
      "The post could not be removed.") ++
    LString.s "<p>".
End Content.

Definition pack (root : LString.t) (is_logged : option bool)
  (content : LString.t) : LString.t :=
  header root is_logged ++ content ++ footer.

Definition content (answer : Http.Answer.t) : LString.t :=
  match answer with
  | Http.Answer.NotFound => LString.s "Not found."
  | Http.Answer.Forbidden => LString.s "Forbidden."
  | Http.Answer.Static _ content => content
  | Http.Answer.Login => pack (LString.s "") None Content.login
  | Http.Answer.Logout => pack (LString.s "") None Content.logout
  | Http.Answer.Public is_logged page =>
    match page with
    | Http.Answer.Public.Index posts =>
      pack (LString.s "") (Some is_logged) @@ Content.index is_logged posts
    | Http.Answer.Public.PostShow url post =>
      pack (LString.s "../../") (Some is_logged) @@ Content.post_show is_logged url post
    end
  | Http.Answer.Private page =>
    match page with
    | Http.Answer.Private.PostAdd =>
      pack (LString.s "../") (Some true) @@ Content.post_add
    | Http.Answer.Private.PostDoAdd is_success =>
      pack (LString.s "../") (Some true) @@ Content.post_do_add is_success
    | Http.Answer.Private.PostEdit url post =>
      pack (LString.s "../../") (Some true) @@ Content.post_edit url post
    | Http.Answer.Private.PostDoEdit url is_success =>
      pack (LString.s "../../") (Some true) @@ Content.post_do_edit url is_success
    | Http.Answer.Private.PostDoDelete is_success =>
      pack (LString.s "../../") (Some true) @@ Content.post_do_delete is_success
    end
  end.
