(lang dune 2.7)
(name ocaml-smtlib)

(source (github ghulette/ocaml-smtlib))
(generate_opam_files true)
(license "MIT")
(maintainers "geoff@hulette.net")
(authors "Geoff Hulette")

(package
  (name ocaml-smtlib)
  (synopsis "A simple OCaml API for building/parsing SMTLIB2 expressions and interacting with some popular SMT solvers")
  (description "
Based on ocaml-z3 by Arjun Guha, with added support for additional SMT solvers.")
  (depends
    (dune (>= 1.10))
    (ocaml (>= "4.02.3"))
    base-unix))
