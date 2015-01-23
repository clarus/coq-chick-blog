(** Pretty-print responses to HTML. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Http.
Require Import Model.
Require Response.

Import ListNotations.
Local Open Scope char.

(** The header of a page with the authentication status (logged in or out). *)
Definition header (is_logged : option bool) : LString.t :=
  LString.s "<!DOCTYPE html>
<html lang=""en"">
  <head>
    <meta charset=""utf-8"">
    <meta name=""viewport"" content=""width=device-width, initial-scale=1"">
    <title>ChickBlog</title>
    <link rel=""stylesheet"" href=""/static/style.min.css"" type=""text/css"" />

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
          <a class=""navbar-brand"" href=""/"">ChickBlog</a>
        </div>" ++
  match is_logged with
  | None => LString.s ""
  | Some is_logged => LString.s "
        <div class=""collapse navbar-collapse"">
          <ul class=""nav navbar-nav"">
            <li><a href=""" ++
  LString.s (if is_logged then "/logout" else "/login") ++ LString.s """>" ++
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

(** The footer of a page. *)
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

(** The MIME type of a page. *)
Definition mime_type (response : Response.t) : LString.t :=
  match response with
  | Response.Static mime_type _ => mime_type
  | _ => LString.s "text/html; charset=utf-8"
  end.

(** Pretty-print the cookies. *)
Definition cookies (response : Response.t) : Http.Cookies.t :=
  match response with
  | Response.Login => [(LString.s "is_logged", LString.s "true")]
  | Response.Logout => [(LString.s "is_logged", LString.s "false")]
  | _ => []
  end.

(** Pretty-print a date as the example "January 1, 1970". *)
Definition date (post_header : Post.Header.t) : LString.t :=
  let date := Post.Header.date post_header in
  Date.Print.full_month date ++ LString.s " " ++
  Date.Print.day None date ++ LString.s ", " ++ Date.Print.year 4 None date.

(** The HTML content of pages. *)
Module Content.
  (** The confirmation of a login. *)
  Definition login : LString.t :=
    LString.s "<p>You are now logged in.</p>".

  (** The confirmation of a logout. *)
  Definition logout : LString.t :=
    LString.s "<p>You are now logged out.</p>".

  (** The index page, with the list of posts. *)
  Definition index (is_logged : bool) (posts : list Post.Header.t) : LString.t :=
    LString.s "<h1>Welcome</h1>
<p>This is a blog written and proven in <a href=""https://coq.inria.fr/"">Coq</a>. The sources are on <a href=""https://github.com/clarus/coq-chick-blog"">GitHub</a>.</p>" ++
    LString.s (if is_logged then "" else "<p><em>You can login to add, edit or remove posts.</em></p>") ++ LString.s "

<h2>Posts" ++
  LString.s (if is_logged then " <small><a href=""/posts/add"">add</a></small>" else "") ++
  LString.s "</h2>
<ul>" ++
  LString.join [LString.Char.n] (posts |> List.map (fun post =>
    LString.s "<li><a href=""/posts/show/" ++ Post.Header.url post ++ LString.s """>" ++
    Post.Header.title post ++ LString.s "</a> " ++ date post ++ LString.s "</li>")) ++
  LString.s "</ul>".

  (** The page to show a post. There is no pre-processing for now on the content
      of a post. *)
  Definition post_show (is_logged : bool) (url : LString.t)
    (post : option Post.t) : LString.t :=
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

  (** The form to add a post. *)
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

  (** Confirmation (or not) that a post was added. *)
  Definition post_do_add (is_success : bool) : LString.t :=
    if is_success then
      LString.s "<p>Post successfully added.</p>"
    else
      LString.s "<p>The post could not be added.</p>".

  (** The form to edit a post. *)
  Definition post_edit (url : LString.t) (post : option Post.t) : LString.t :=
    match post with
    | None => LString.s "<p>Post not found.</p>"
    | Some post =>
      let header := Post.header post in
      LString.s "<h1>" ++ Post.Header.title header ++ LString.s "</h1>
<p><em>" ++ date header ++ LString.s "</em></p>
<form action=""/posts/do_edit/" ++ url ++ LString.s """ method=""GET"">
  <div class=""form-group"">
    <textarea class=""form-control"" name=""content"" rows=""5"">" ++
    Post.content post ++ LString.s "</textarea>
  </div>
  <button type=""submit"" class=""btn btn-default"">Submit</button>
</form>"
    end.

  (** Confirmation (or not) that a post was edited. *)
  Definition post_do_edit (url : LString.t) (is_success : bool) : LString.t :=
    LString.s "<p>" ++
    LString.s (if is_success then
      "Post successfully updated."
    else
      "The post could not be updated.") ++
    LString.s "<p>
<p><a href=""/posts/show/" ++ url ++ LString.s """>Back to the post.</a></p>".

  (** Confirmation (or not) that a post was deleted. *)
  Definition post_do_delete (is_success : bool) : LString.t :=
    LString.s "<p>" ++
    LString.s (if is_success then
      "Post successfully removed."
    else
      "The post could not be removed.") ++
    LString.s "<p>".
End Content.

(** Add a header and a footer to an HTML content. *)
Definition pack (is_logged : option bool) (content : LString.t) : LString.t :=
  header is_logged ++ content ++ footer.

(** Pretty-print a response to HTML. *)
Definition content (response : Response.t) : LString.t :=
  match response with
  | Response.NotFound => LString.s "Not found."
  | Response.WrongArguments => LString.s "Wrong arguments."
  | Response.Forbidden => LString.s "Forbidden."
  | Response.Static _ content => content
  | Response.Login => pack None Content.login
  | Response.Logout => pack None Content.logout
  | Response.Public is_logged page =>
    match page with
    | Response.Public.Index posts =>
      pack (Some is_logged) @@ Content.index is_logged posts
    | Response.Public.PostShow url post =>
      pack (Some is_logged) @@ Content.post_show is_logged url post
    end
  | Response.Private page =>
    match page with
    | Response.Private.PostAdd =>
      pack (Some true) @@ Content.post_add
    | Response.Private.PostDoAdd is_success =>
      pack (Some true) @@ Content.post_do_add is_success
    | Response.Private.PostEdit url post =>
      pack (Some true) @@ Content.post_edit url post
    | Response.Private.PostDoEdit url is_success =>
      pack (Some true) @@ Content.post_do_edit url is_success
    | Response.Private.PostDoDelete is_success =>
      pack (Some true) @@ Content.post_do_delete is_success
    end
  end.

(** A raw response is the MIME type, the cookies and the pretty-printed body. *)
Definition raw (response : Response.t) : Response.Raw.t :=
  Response.Raw.New (mime_type response) (cookies response) (content response).
