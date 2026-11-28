;; Module variables belong to script commands, including binary modules.
(module $source binary
  "\00asm\01\00\00\00"
  "\06\06\01\7f\00\41\07\0b"
  "\07\05\01\01g\03\00")
(module binary "\00asm\01\00\00\00")
(register "source" $source)
(assert_return (get $source "g") (i32.const 7))
