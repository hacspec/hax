(lang dune 3.8)
(using coq 0.8)
(generate_opam_files true)
(name coq-hacspec)
(opam_file_location inside_opam_directory)

(package
 (name coq-hacspec)
 (synopsis "A short synopsis")
 (description "A longer description")
 (maintainers "Lasse Letager Hansen<letager@cs.au.dk>")
 (authors "Lasse Letager Hansen<letager@cs.au.dk>")
 (depends
        ocaml
        dune
        (base (>= "0.16.2"))
	(coq (>= "8.18.0"))
        coq-compcert
        coq-coqprime
        coq-quickchick
        )
 (tags
  (topics "to describe" your project)))

