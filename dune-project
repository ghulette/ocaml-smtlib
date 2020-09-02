(lang dune 2.7)
(name easy-smt)

(source (github ghulette/ocaml-smtlib))
(generate_opam_files true)
(license "MIT")
(maintainers "geoff@hulette.net")
(authors "Geoff Hulette")

(package
  (name easy-smt)
  (synopsis "An OCaml API for working with popular SMT solvers")
  (description "
Based on ocaml-z3 by Arjun Guha, with added support for additional SMT solvers.")
  (depends
    (dune (>= 1.10))
    (ocaml (>= "4.02.3"))
    base-unix))
