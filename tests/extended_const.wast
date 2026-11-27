;; Binary fixture: two immutable globals evaluating ((7 + 9) - 3) * 4,
;; in i32 and i64 respectively. Exercises actual extracted binary parsing,
;; module validation, instantiation, and export lookup.
(module binary
  "\00\61\73\6d\01\00\00\00\06\1d\02\7f\00\41\07\41\09\6a\41\03\6b\41\04\6c\0b\7e\00\42\07\42\09\7c\42\03\7d\42\04\7e\0b\07\0d\02\03\69\33\32\03\00\03\69\36\34\03\01")
(assert_return (get "i32") (i32.const 52))
(assert_return (get "i64") (i64.const 52))
(assert_invalid
  (module (global i32 (i32.add (i32.const 1))))
  "type mismatch")
(assert_invalid
  (module (global i32 (i32.add (i32.const 1) (i64.const 2))))
  "type mismatch")
(assert_invalid
  (module (global i32 (i32.div_u (i32.const 1) (i32.const 1))))
  "constant expression required")
