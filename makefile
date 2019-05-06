all: evaluation expr miniml_lex miniml_parse miniml

evaluation: evaluation.ml
	ocamlbuild -just-plugin
	ocamlbuild -package unix 
	ocamlbuild -lib unix evaluation.byte

expr: expr.ml
	ocamlbuild -lib unix expr.byte

miniml_lex: miniml_lex.mll
	ocamlbuild -lib unix miniml_lex.byte

miniml_parse: miniml_parse.mly
	ocamlbuild -lib unix miniml_parse.byte

miniml: miniml.ml
	ocamlbuild -lib unix miniml.byte
