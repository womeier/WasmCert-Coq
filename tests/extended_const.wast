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

;; Binary fixture: g0 = 7; g1 = g0 + 5; g2 = g1 * g0.
(module binary
  "\00\61\73\6d\01\00\00\00\06\16\03\7f\00\41\07\0b\7f\00\23\00\41\05\6a\0b\7f\00\23\01\23\00\6c\0b\07\11\02\05\63\68\61\69\6e\03\02\05\66\69\72\73\74\03\00")
(assert_return (get "chain") (i32.const 84))
(assert_return (get "first") (i32.const 7))

;; Defined globals are also available in data offsets and element expressions.
(module
  (type $t (func (result i32)))
  (global $offset i32 (i32.const 0))
  (global $base i64 (i64.const 17))
  (global (export "wide") i64 (i64.sub (global.get $base) (i64.const 2)))
  (global $reference funcref (ref.func $target))
  (global $copy funcref (global.get $reference))
  (table 1 funcref)
  (memory 1)
  (elem (global.get $offset) funcref (global.get $copy))
  (data (i32.add (global.get $offset) (i32.const 3)) "x")
  (func $target (type $t) (i32.const 37))
  (func (export "call") (result i32)
    (call_indirect (type $t) (global.get $offset)))
  (func (export "load") (result i32) (i32.load8_u (i32.const 3))))
(assert_return (get "wide") (i64.const 15))
(assert_return (invoke "call") (i32.const 37))
(assert_return (invoke "load") (i32.const 120))

(assert_invalid
  (module (global i32 (global.get 0)))
  "unknown global")
(assert_invalid
  (module (global i32 (global.get 1)) (global i32 (i32.const 0)))
  "unknown global")
(assert_invalid
  (module (global (mut i32) (i32.const 0)) (global i32 (global.get 0)))
  "constant expression required")
(assert_invalid
  (module (global (mut i32) (i32.const 0)) (memory 1) (data (global.get 0) "x"))
  "constant expression required")
(assert_invalid
  (module (global (mut funcref) (ref.null func))
    (table 1 funcref) (elem (i32.const 0) funcref (global.get 0)))
  "constant expression required")

;; A nonempty original store and imported global addresses must not perturb
;; defined-global allocation or function addresses.
(module $provider
  (global (export "base") i32 (i32.const 40)))
(register "ec_provider")
(module
  (import "ec_provider" "base" (global $import i32))
  (global $a i32 (i32.add (global.get $import) (i32.const 1)))
  (global (export "answer") i32 (i32.add (global.get $a) (i32.const 1))))
(assert_return (get "answer") (i32.const 42))
