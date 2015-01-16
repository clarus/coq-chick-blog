# ChickBlog
A blog engine written and proven in Coq.

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

    Definition server (path : Request.Path.t) (cookies : Request.Cookies.t)
      : C.t Answer.t.

It handles an HTTP request and generate an answer using system calls to the file system. The type `C.t A` represents computations of type `A` doing I/O operations:

    Inductive t (A : Type) : Type :=
    | Ret : forall (x : A), t A
    | Call : forall (command : Command.t), (Command.answer command -> t A) -> t A.

We can either:

* return a pure value
* call an external command and wait for its result

The purity of Coq ensures that each request is answered in finite time with no errors. We specify the behavior of the server in `Spec.v`.
