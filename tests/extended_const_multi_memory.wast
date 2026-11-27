;; Integration fixture for extended-const plus the pinned multi-memory codec.
;; g0 = 0; g1 = g0 + 3. An active data segment writes 42 at offset g1
;; in memory 1. "run" reads memory 1; "peek" verifies memory 0 is untouched.
;; All module syntax is binary: no new text frontend support is involved.
(module binary
  "\00\61\73\6d\01\00\00\00\01\05\01\60\00\01\7f\03\03\02\00\00\05\05\02\00\01\00\01\06\0e\02\7f\00\41\00\0b\7f\00\23\00\41\03\6a\0b\07\0e\02\03\72\75\6e\00\00\04\70\65\65\6b\00\01\0a\12\02\08\00\41\03\2d\40\01\00\0b\07\00\41\03\2d\00\00\0b\0b\08\01\02\01\23\01\0b\01\2a")
(assert_return (invoke "run") (i32.const 42))
(assert_return (invoke "peek") (i32.const 0))
