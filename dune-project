(lang dune 1.11)

(dialect
 (name imandra)
 (implementation
  (extension iml)
  (preprocess  (system "imandra-extract %{input-file}")))
 (interface (extension "imli")))