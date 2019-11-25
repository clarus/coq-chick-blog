OUTPUT = chickBlog.native

build:
	ocamlbuild $(OUTPUT) -use-ocamlfind -package cohttp-lwt-unix,lwt,lwt.unix,num,str -tag thread

clean:
	rm -Rf _build/
	rm $(OUTPUT)
