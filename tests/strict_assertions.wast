;; Positive stage distinctions. No text frontend extension is needed.
(assert_malformed
  (module binary "\00asm\01\00\00\00\ff")
  "malformed")
(assert_invalid
  (module (func (result i32)))
  "type mismatch")
(assert_unlinkable
  (module (import "missing" "f" (func)))
  "unknown import")
(assert_trap
  (module (func $start unreachable) (start $start))
  "unreachable")
