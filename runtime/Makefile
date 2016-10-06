all: mwu.mli mwu.ml
	ocamlbuild mwu.native

mwu.ml:
	cd ../ && rm routing.vo && make && cd runtime
