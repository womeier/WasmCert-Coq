;; Binary projections of the six final Core 3.0 tests whose expectations differ
;; from the historical extended-const proposal suite. No text parser changes.
;;
;; Final source: WebAssembly/spec d7aada502455b3d9176ca4cbe48be4724d511d2a,
;; test/core/global.wast:373-374, data.wast:89-90, elem.wast:178-185.
;; They are ordinary successful module commands, NOT assert_invalid.
;; Historical source: WebAssembly/extended-const
;; 8d4f6aa2b00a8e7c0174410028625c6a176db8a1:
;; global.wast:363-370, data.wast:84-91, elem.wast:170-177 instead wrap
;; the same modules in assert_invalid "unknown global".
;;
;; Numeric and named references resolve to the same binary global index, so
;; each pair intentionally has identical bytes. Source expectations are not
;; patched or suppressed. The historical suites are still run and reported.

;; (module (global i32 (i32.const 0)) (global i32 (global.get 0)))
(module binary
  "\00\61\73\6d\01\00\00\00\06\0b\02\7f\00\41\00\0b\7f\00\23\00\0b")
;; (module (global $g i32 (i32.const 0)) (global i32 (global.get $g)))
(module binary
  "\00\61\73\6d\01\00\00\00\06\0b\02\7f\00\41\00\0b\7f\00\23\00\0b")

;; (module (memory 1) (global i32 (i32.const 0)) (data (global.get 0) "a"))
(module binary
  "\00\61\73\6d\01\00\00\00\05\03\01\00\01\06\06\01\7f\00\41\00\0b\0b\07\01\00\23\00\0b\01\61")
;; (module (memory 1) (global $g i32 (i32.const 0)) (data (global.get $g) "a"))
(module binary
  "\00\61\73\6d\01\00\00\00\05\03\01\00\01\06\06\01\7f\00\41\00\0b\0b\07\01\00\23\00\0b\01\61")

;; (module (global i32 (i32.const 0))
;;   (table 1 funcref) (elem (global.get 0) $f) (func $f))
(module binary
  "\00\61\73\6d\01\00\00\00\01\04\01\60\00\00\03\02\01\00\04\04\01\70\00\01\06\06\01\7f\00\41\00\0b\09\07\01\00\23\00\0b\01\00\0a\04\01\02\00\0b")
;; (module (global $g i32 (i32.const 0))
;;   (table 1 funcref) (elem (global.get $g) $f) (func $f))
(module binary
  "\00\61\73\6d\01\00\00\00\01\04\01\60\00\00\03\02\01\00\04\04\01\70\00\01\06\06\01\7f\00\41\00\0b\09\07\01\00\23\00\0b\01\00\0a\04\01\02\00\0b")
