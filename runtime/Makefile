all: mwu.mli mwu.ml server.native
	ocamlbuild -use-ocamlfind mwu.native

server.native: mwu.mli mwu.ml
	ocamlbuild -use-ocamlfind server.native

mwu.ml:
	cd ../ && rm routing.vo && make && cd runtime
