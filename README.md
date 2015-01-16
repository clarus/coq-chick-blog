# ChickBlog
A blog engine written and proven in [Coq](https://coq.inria.fr/).

This is a demo blog engine where an user can login (no passwords), add, edit or delete posts. The code is written mostly in Coq, compiled to OCaml and linked to the [CoHTTP](https://github.com/mirage/ocaml-cohttp) library to handle the HTTP protocol.

The aim of this project is to demonstrate that applications with I/Os can be written and specified more naturally using the (new) concept of [symbolic simulations in Coq](http://coq-blog.clarus.me/checking-concurrent-programs-with-symbolic-simulations.html).

## Run
Add the Coq repositories with [OPAM](https://opam.ocaml.org/):

    opam repo add coq-stable https://github.com/coq/repo-stable.git
    opam repo add coq-unstable https://github.com/coq/repo-unstable.git

Install the dependencies:

    opam install --jobs=4 coq:list-string coq:error-handlers coq:function-ninjas coq:moment
    opam install --jobs=4 lwt cohttp

Download the CSS:

    mkdir -p extraction/static
    curl -L https://github.com/clarus/coq-red-css/releases/download/coq-blog.1.0.2/style.min.css >extraction/static/style.min.css

Compile:

    ./configure.sh && make
    cd extraction/
    make

Run on [localhost:8008](http://localhost:8008/):

    ./chickBlog.native

## Specification
The blog is defined in `Main.v` as the function:

    Definition server (path : Request.Path.t) (cookies : Request.Cookies.t) : C.t Answer.t.

It handles an HTTP request and generate an answer using system calls to the file system. The type `C.t A` represents a computation doing I/O operations:

    Inductive t (A : Type) : Type :=
    | Ret : forall (x : A), t A
    | Call : forall (command : Command.t), (Command.answer command -> t A) -> t A.

It can either:

* return a pure value of type `A`
* call an external command and wait for its result

The purity of Coq ensures that each request is answered in finite time without errors. We specify the behavior of the server in `Spec.v`.
