# MicroBlog
A micro-blogging web application in Coq.

## Run
Add the Coq repositories with [OPAM](https://opam.ocaml.org/):

    opam repo add coq-stable https://github.com/coq/repo-stable.git
    opam repo add coq-unstable https://github.com/coq/repo-unstable.git

Install the dependencies:

    opam install --jobs=4 coq:list-string coq:error-handlers coq:function-ninjas
    opam install --jobs=4 lwt cohttp

Compile:

    ./configure.sh && make
    cd extraction/
    curl -L https://github.com/clarus/coq-red-css/releases/download/coq-blog.1.0.2/style.min.css >style.min.css
    make

Run on [localhost:8008](http://localhost:8008/):

    ./microBlog.native
