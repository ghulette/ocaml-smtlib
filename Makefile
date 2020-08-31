SOURCES  = smtlib_parser.mly smtlib_lexer.mll smtlib_syntax.ml smtlib.mli smtlib.ml
RESULT   = smtlib
PACKS    = unix
ANNOTATE = yes
TRASH    = *.cmt *.cmti

all: ncl bcl

install : libinstall
remove : libuninstall

-include OCamlMakefile
