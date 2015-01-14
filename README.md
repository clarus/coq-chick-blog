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

    curl -L https://github.com/clarus/coq-red-css/releases/download/coq-blog.1.0.2/style.min.css >extraction/static/style.min.css

Compile:

    ./configure.sh && make
    cd extraction/
    make

Run on [localhost:8008](http://localhost:8008/):

    ./chickBlog.native
