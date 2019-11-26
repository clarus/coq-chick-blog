# ChickBlog
> A blog engine written and proven in [Coq](https://coq.inria.fr/).

This is a demo blog engine where a user can login (no passwords), add, edit or delete posts. The code is written mostly in Coq, compiled to OCaml and linked to the [CoHTTP](https://github.com/mirage/ocaml-cohttp) library to handle the HTTP protocol.

The aim of this project is to demonstrate that applications with I/Os can be written and specified naturally using the (new) concept of [symbolic simulations in Coq](http://coq-blog.clarus.me/checking-concurrent-programs-with-symbolic-simulations.html).

## Install
Add the Coq repository with [opam](https://opam.ocaml.org/) if not already done:
```
opam repo add coq-released https://coq.inria.fr/opam/released
```
Install the package:
```
opam install coq-chick-blog
```
Run:
```
coq-chick-blog
```
You can now open [localhost:8008](http://localhost:8008/) to navigate the blog. Posts will be saved in the current folder. There is not password for this demo project.

To build the project by hand for development, read the build instructions from the `coq-chick-blog.opam` file.

## Specification
The blog is defined in `Main.v` as the function:
```coq
Definition server (path : Path.t) (cookies : Cookies.t) : C.t Response.t.
```

It handles an HTTP request and generate an answer using system calls to the file system. The type `C.t A` represents a computation doing I/O operations:
```coq
Inductive t (A : Type) : Type :=
| Ret : forall (x : A), t A
| Call : forall (command : Command.t), (Command.answer command -> t A) -> t A.
```

A computation can either:

* return a pure value of type `A`
* call an external command and wait for its result

The purity of Coq ensures that each request is answered exactly once in finite time. We specify the behavior of the server in `Spec.v`.

### Scenarios
A scenario is a set of runs of the server. A type-checking scenario shows that the server behaves as expected in a certain use case. For example, we check that when we create, edit and view a post we get the same result as what we entered. You can think of a scenario as a unit test with universally quantified variables.

Here is a simple check of the execution of the index page:
```coq
(** The index page when the list of posts is available. *)
Definition index_ok (cookies : Cookies.t) (post_headers : list Post.Header.t)
    : Run.t (Main.server Path.Index cookies).
    (* The handler asks the list of available posts. We return `post_headers`. *)
    apply (Call (Command.ListPosts _ ) (Some post_headers)).
    (* The handler terminates without other system calls. *)
    apply (Ret (Response.Index (Cookies.is_logged cookies) post_headers)).
Defined.
```

Given any `cookies` and `post_headers`, we execute the server handler on the page `Request.Path.Index`. The handler does exactly one system call, to which we answer `Some post_headers`, playing the role of the system. The final response of the server is then `Response.Public.Index post_headers`. Note that we do not need to execute `index_ok` on every instances of `cookies` and `post_headers`: since the type-system of Coq is supposed sound, it is enough to type-check `index_ok`.

### Privacy
We check that, for any runs of a program, an unauthenticated user cannot access private pages (like edit) or modify the file system with system calls.

## License
All the code is under the open-source MIT license.
