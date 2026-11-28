"""Exercise actual extracted binary parsing, validation and execution.

Fixtures are encoded directly, not passed through the deferred text frontend.
The module has two () -> i32 functions, exports the second as main, and
declares the first for ref.func unless a table initializer declares it instead.
"""
import pathlib
import re
import subprocess
import sys
import tempfile


def module(body, table=None, declare=True, imports=None, globals=None):
    prefix = bytes.fromhex(
        "0061736d01000000 0105016000017f"
    )
    if imports is not None:
        payload = bytes.fromhex(imports)
        assert len(payload) < 128
        prefix += b"\x02" + bytes([len(payload)]) + payload
    prefix += bytes.fromhex("0303020000")
    if table is not None:
        payload = bytes.fromhex(table)
        assert len(payload) < 128
        prefix += b"\x04" + bytes([len(payload)]) + payload
    if globals is not None:
        payload = bytes.fromhex(globals)
        assert len(payload) < 128
        prefix += b"\x06" + bytes([len(payload)]) + payload
    prefix += bytes.fromhex("070801046d61696e0001")
    if declare:
        prefix += bytes.fromhex("09050103000100")
    first = bytes.fromhex("0400412a0b")
    second = bytes([len(body) + 2, 0]) + body + b"\x0b"
    code = b"\x02" + first + second
    assert len(code) < 128
    return prefix + b"\x0a" + bytes([len(code)]) + code


cases = [
    ("function", "d200d4d1", 0, "i32.const 0"),
    ("function_identity", "d200d4d4d1", 0, "i32.const 0"),
    ("null_function", "d070d4d1", 0, "Execution returned a trap"),
    ("null_external", "d06fd4d1", 0, "Execution returned a trap"),
    ("numeric_operand", "4100d4", 123, "instantiation error:"),
    ("missing_operand", "d4", 123, "instantiation error:"),
    ("unreachable", "00d41a4107", 0, "Execution returned a trap"),
    # Genuine invalid operands: these must reach validation, not fail decoding.
    # Positive typed-call validation still depends on closed indexed types.
    ("numeric_call_ref", "41001400", 123, "instantiation error:"),
    ("numeric_return_call_ref", "41001500", 123, "instantiation error:"),
    ("missing_call_ref_operand", "1400", 123, "instantiation error:"),
    ("truncated_call_ref_index", "1480", 123, "error in parsing module"),
    ("overflow_call_ref_index", "148080808010", 123, "error in parsing module"),
    ("branch_function", "0270d200d600d0700bd1", 0, "i32.const 0"),
    ("branch_null_fallthrough", "0270d070d600d0700bd1", 0, "i32.const 1"),
    ("branch_external_null", "026fd06fd600d06f0bd1", 0, "i32.const 1"),
    ("branch_missing_ref_result", "0240d070d6000b4107", 123, "instantiation error:"),
    ("branch_numeric_result", "027fd070d60041070b", 123, "instantiation error:"),
    ("branch_numeric_operand", "02704100d600d0700bd1", 123, "instantiation error:"),
    ("branch_invalid_label", "d070d6014107", 123, "instantiation error:"),
    ("nonnull_ref_func_block", "026470d2000bd1", 0, "i32.const 0"),
    ("nonnull_refinement_trap", "026470d070d40bd1", 0, "Execution returned a trap"),
    ("nullable_cannot_satisfy_nonnull", "026470d0700bd1",
     123, "Module type checking failure:"),
    ("ref_null_requires_heap_not_reference_type", "d06370d1",
     123, "error in parsing module"),
    ("null_branch_consumes_reference", "027f412ad070d5001a1a41070b",
     0, "i32.const 42"),
    ("nonnull_null_branch_retains_reference", "027f412ad200d5001a1a41070b",
     0, "i32.const 7"),
    ("external_null_branch", "027f412ad06fd5001a1a41070b",
     0, "i32.const 42"),
    ("null_branch_numeric_operand", "4100d500", 123, "Module type checking failure:"),
    ("null_branch_missing_operand", "d500", 123, "Module type checking failure:"),
    ("null_branch_invalid_label", "d070d501", 123, "Module type checking failure:"),
    ("null_branch_missing_label_argument", "d070d500", 123, "Module type checking failure:"),
    ("null_branch_truncated_index", "d580", 123, "error in parsing module"),
    ("null_branch_overflow_index", "d58080808010", 123, "error in parsing module"),
]

table_cases = [
    ("table_function_initializer", "41002500d141012500d16a",
     "014000700002d2000b", 0, "i32.const 0"),
    ("table_null_initializer", "41002500d141012500d16a",
     "014000700002d0700b", 0, "i32.const 2"),
    ("table_forward_function", "41002500d141012500d16a",
     "014000700002d2010b", 0, "i32.const 0"),
    ("table_initialized_call", "4100110000",
     "014000700002d2000b", 0, "i32.const 42"),
    ("table_null_initializer_call_traps", "4100110000",
     "014000700001d0700b", 0, "Execution returned a trap"),
    ("table_zero_initializer_declares_function", "d200d1",
     "014000700000d2000b", 0, "i32.const 0"),
    ("table_zero_stays_empty", "4100110000",
     "014000700000d2000b", 0, "Execution returned a trap"),
    ("table_zero_wrong_initializer_type", "4107",
     "01400070000041000b", 123, "Module type checking failure:"),
    ("table_zero_empty_initializer", "4107",
     "0140007000000b", 123, "Module type checking failure:"),
    ("table_zero_unknown_initializer_function", "4107",
     "014000700000d2020b", 123, "Module type checking failure:"),
    ("table_wrong_initializer_reference_kind", "4107",
     "014000700001d06f0b", 123, "Module type checking failure:"),
    ("table_nonconstant_initializer", "4107",
     "014000700000d200d40b", 123, "Module type checking failure:"),
    ("table_invalid_limits", "4107",
     "01400070010201d2000b", 123, "Module type checking failure:"),
    ("table_bad_reserved_byte", "4107",
     "014001700002d2000b", 123, "error in parsing module"),
    ("table_missing_reserved_byte", "4107",
     "0140700002d2000b", 123, "error in parsing module"),
    ("table_missing_initializer_end", "4107",
     "014000700002d200", 123, "error in parsing module"),
    ("table_legacy_default", "41002500d141012500d16a",
     "01700002", 0, "i32.const 2"),
    ("table_nonnull_function_initializer", "41002500d141012500d16a",
     "01400064700002d2000b", 0, "i32.const 0"),
    ("table_nonnull_indirect_call", "4100110000",
     "01400064700001d2000b", 0, "i32.const 42"),
    ("table_nonnull_indirect_tail_call", "4100130000",
     "01400064700001d2000b", 0, "i32.const 42"),
    ("table_nonnull_default_rejected", "4107",
     "0164700002", 123, "Module type checking failure:"),
    ("table_nonnull_null_initializer_rejected", "4107",
     "01400064700002d0700b", 123, "Module type checking failure:"),
    ("table_explicit_nullable_default", "41002500d1",
     "0163700001", 0, "i32.const 1"),
    ("table_nullable_refined_nonnull_result", "02647041002500d40bd1",
     "014000700001d2000b", 0, "i32.const 0"),
    ("table_nullable_without_refinement_rejected", "026470410025000bd1",
     "014000700001d2000b", 123, "Module type checking failure:"),
    ("table_nullable_branches_to_nonnull_label", "02647041002500d600000bd1",
     "014000700001d2000b", 0, "i32.const 0"),
    ("table_null_nonnull_branch_falls_through", "02647041002500d600000bd1",
     "014000700001d0700b", 0, "Execution returned a trap"),
    ("table_null_branch_refines_fallthrough_for_nonnull_store",
     "410041002500d500260141002501d1",
     "024000700001d2000b400064700001d2000b", 0, "i32.const 0"),
    ("table_null_branch_skips_nonnull_store",
     "410741002500d500260141002501d1",
     "024000700001d0700b400064700001d2000b", 0, "i32.const 7"),
]

exe = str(pathlib.Path(sys.argv[1]).resolve())


def check_case(directory, name, body, status, expected, *, table=None, declare=True):
    path = pathlib.Path(directory) / (name + ".wasm")
    path.write_bytes(module(bytes.fromhex(body), table, declare))
    result = subprocess.run(
        [exe, str(path), "-r", "main"], capture_output=True, text=True
    )
    output = re.sub(r"\x1b\[[0-9;]*m", "", result.stdout + result.stderr)
    if result.returncode != status or expected not in output:
        raise AssertionError(
            f"{name}: exit {result.returncode}, expected {status}; {output!r}"
        )


def check_imported_initializer(directory):
    # Binary modules bypass the deferred WAT frontend.
    provider = bytes.fromhex(
        "0061736d01000000 0606016f00d06f0b 07050101670300"
    )
    consumer = module(
        bytes.fromhex("41002500d141012500d16a"),
        table="0140006f000223000b",
        declare=False,
        imports="0103656e760167036f00",
        globals="017f0041070b",
    )

    def binary_module(data):
        return '(module binary "' + "".join(f"\\{b:02x}" for b in data) + '")'

    path = pathlib.Path(directory) / "table_imported_immutable.wast"
    script = binary_module(provider) + '\n(register "env")\n'
    script += binary_module(consumer) + "\n"
    script += '(assert_return (invoke "main") (i32.const 2))\n'
    path.write_text(script)
    result = subprocess.run([exe, "--wast", str(path)], capture_output=True, text=True)
    output = re.sub(r"\x1b\[[0-9;]*m", "", result.stdout + result.stderr)
    ok = result.returncode == 0 and "Result: 4/4 (100.00%)" in output
    if not ok:
        raise AssertionError(f"table_imported_immutable: exit {result.returncode}; {output!r}")


def check_exported_reference_argument(directory):
    data = bytes.fromhex(
        "0061736d01000000 010a026000017f60016f017f 0303020001 "
        "070801046d61696e0001 0a0c020400412a0b05002000d10b"
    )
    encoded = "".join(f"\\{b:02x}" for b in data)
    path = pathlib.Path(directory) / "exported_reference_argument.wast"
    path.write_text(
        f'(module binary "{encoded}")\n'
        '(assert_return (invoke "main" (ref.extern 23)) (i32.const 0))\n'
        '(assert_return (invoke "main" (ref.null extern)) (i32.const 1))\n'
    )
    result = subprocess.run([exe, "--wast", str(path)], capture_output=True, text=True)
    output = re.sub(r"\x1b\[[0-9;]*m", "", result.stdout + result.stderr)
    if result.returncode != 0 or "Result: 3/3 (100.00%)" not in output:
        raise AssertionError(f"exported_reference_argument: exit {result.returncode}; {output!r}")


with tempfile.TemporaryDirectory() as directory:
    for name, body, status, expected in cases:
        check_case(directory, name, body, status, expected)
    for name, body, table, status, expected in table_cases:
        check_case(directory, name, body, status, expected, table=table, declare=False)
    check_imported_initializer(directory)
    check_exported_reference_argument(directory)

total = len(cases) + len(table_cases) + 2
print(f"function-reference binary runtime regressions: {total}/{total}")
