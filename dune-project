(lang dune 3.8)

(using coq 0.8)

(name bigatomic)

(generate_opam_files)

(license MIT)

(authors "Anonymous")

(maintainers "Anonymous")

(source
 (github anonymous/anonymous))

(package
 (name bigatomic)
 (synopsis "Mechanization of bigatomic")
 (depends
  (coq
   (>= 8.16))
  (coq-stdpp
   (>= 1.10.0))
  (coq-iris
   (>= 4.3.0))))
