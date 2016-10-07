all: mwu.mli mwu.ml
	ocamlbuild -use-ocamlfind mwu.native

mwu.ml:
	cd ../ && rm routing.vo && make && cd runtime
