(lang dune 3.8)
(using coq 0.8)
(generate_opam_files true)
(name coq-hacspec-ssprove)
(opam_file_location inside_opam_directory)

(package
 (name coq-hacspec-ssprove)
 (synopsis "A short synopsis")
 (description "A longer description")
 (maintainers "Lasse Letager Hansen<letager@cs.au.dk>")
 (authors "Lasse Letager Hansen<letager@cs.au.dk>")
 (depends
        ocaml
        dune
        (base (>= "0.16.2"))
	(jasmin (= "dev"))
	(ssprove (= "dev"))
	coq-stdpp
	(coq-mathcomp-word (>= "3.0"))
	(coq-mathcomp-zify (>= "1.5.0+2.0+8.16"))
	(coq-concert (= "dev"))
	(coq (>= "8.18.0"))
        )
 (tags
  (topics "to describe" your project)))
