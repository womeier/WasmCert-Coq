;; Cross-proposal dependency fixtures, NOT a passing current-AST gate.
;; Encoded by wasm-tools 1.263.0; see extended_const_official_projection.md.
;; The first three modules validate under the final spec. The final module
;; decodes, then fails validation: table initializers cannot read this global.

;; (module (func $f) (table 1 funcref)
;;   (elem (i32.const 0) (ref func) (ref.func $f)))
(module binary
  "\00\61\73\6d\01\00\00\00\01\04\01\60\00\00\03\02\01\00"
  "\04\04\01\70\00\01\09\0c\01\06\00\41\00\0b\64\70\01\d2\00\0b"
  "\0a\04\01\02\00\0b\00\0b\04\6e\61\6d\65\01\04\01\00\01\66")

;; (module (func $f) (table 1 (ref func) (ref.func $f)))
(module binary
  "\00\61\73\6d\01\00\00\00\01\04\01\60\00\00\03\02\01\00"
  "\04\0a\01\40\00\64\70\00\01\d2\00\0b"
  "\0a\04\01\02\00\0b\00\0b\04\6e\61\6d\65\01\04\01\00\01\66")

;; (module (table 1 funcref (ref.null func)))
(module binary
  "\00\61\73\6d\01\00\00\00\04\09\01\40\00\70\00\01\d0\70\0b")

;; (module (global $g funcref (ref.null func))
;;   (table 1 funcref (global.get $g)))
(assert_invalid
  (module binary
    "\00\61\73\6d\01\00\00\00\04\09\01\40\00\70\00\01\23\00\0b"
    "\06\06\01\70\00\d0\70\0b\00\0b\04\6e\61\6d\65\07\04\01\00\01\67")
  "unknown global")
