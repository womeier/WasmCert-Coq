;; Every assertion below must FAIL, even though loading each module fails.
(assert_malformed (module (func (result i32))) "not malformed")
(assert_invalid
  (module binary "\00asm\01\00\00\00\ff")
  "not invalid")
(assert_invalid
  (module (import "missing" "f" (func)))
  "not invalid")
(assert_invalid
  (module (func $start unreachable) (start $start))
  "not invalid")
(assert_unlinkable
  (module (func $start unreachable) (start $start))
  "not unlinkable")
(assert_trap
  (module (import "missing" "f" (func)))
  "not uninstantiable")
