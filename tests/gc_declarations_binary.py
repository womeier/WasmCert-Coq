"""Production recursive/composite type sections; no text parser or assembler."""
import pathlib
import re
import subprocess
import sys
import tempfile


def section(number, contents):
    assert len(contents) < 128
    return bytes([number, len(contents)]) + contents


def module(groups, function_index=None, body="4107"):
    result = bytes.fromhex("0061736d01000000")
    result += section(1, bytes([len(groups)]) + b"".join(bytes.fromhex(g) for g in groups))
    if function_index is None:
        return result
    result += section(3, bytes([1, function_index]))
    result += section(7, bytes.fromhex("01046d61696e0000"))
    code = b"\x00" + bytes.fromhex(body) + b"\x0b"
    result += section(10, bytes([1, len(code)]) + code)
    return result


function = "6000017f"
cases = [
    ("struct_before_function", ["5f017800", function], 1, "4107", 0, "i32.const 7"),
    ("array_before_function", ["5e7701", function], 1, "4107", 0, "i32.const 7"),
    ("explicit_recursive_group", ["4e025f006000017f"], 1, "4107", 0, "i32.const 7"),
    ("two_aggregate_kinds", ["4e025f005e7800", function], 2, "4107", 0, "i32.const 7"),
    ("self_recursive_structure", ["5f01630000", function], 1, "4107", 0, "i32.const 7"),
    ("mutual_recursive_structures", ["4e025f016301005f01630000", function],
     2, "4107", 0, "i32.const 7"),
    ("struct_width_subtype", ["50005f00", "4f01005f017800", function],
     2, "4107", 0, "i32.const 7"),
    ("immutable_covariance", ["50005f016d00", "4f01005f016c00", function],
     2, "4107", 0, "i32.const 7"),
    ("array_covariance", ["50005e6d00", "4f01005e6c00", function],
     2, "4107", 0, "i32.const 7"),
    ("function_variance", ["500060016d016d", "4f010060016e016c", function],
     2, "4107", 0, "i32.const 7"),
    ("i31_with_composite_context", ["5f00", "5e7800", function],
     2, "417ffb1cfb1e", 0, "i32.const 2147483647"),
    ("final_parent", ["5f00", "4f01005f00", function],
     2, "4107", 123, "instantiation error:"),
    ("mutable_covariance", ["50005f016d01", "4f01005f016c01", function],
     2, "4107", 123, "instantiation error:"),
    ("packed_width_subtyping", ["50005e7800", "4f01005e7700", function],
     2, "4107", 123, "instantiation error:"),
    ("cross_kind_subtyping", ["50005f00", "4f01005e7800", function],
     2, "4107", 123, "instantiation error:"),
    ("dangling_field_type", ["5f01630200", function],
     1, "4107", 123, "instantiation error:"),
    ("forward_reference_outside_group", ["5f01630100", function],
     1, "4107", 123, "instantiation error:"),
    ("function_index_is_struct", ["5f00", function],
     0, "4107", 123, "instantiation error:"),
    ("block_index_is_struct", ["5f00", function],
     1, "02000b4107", 123, "instantiation error:"),
    ("bad_field_mutability", ["5f017802", function],
     1, "4107", 123, "error in parsing module"),
    ("truncated_recursive_vector", ["4e025f00"],
     None, "", 123, "error in parsing module"),
    ("multiple_supertypes", ["50005f00", "4f0200005f00", function],
     2, "4107", 123, "instantiation error:"),
    ("reversed_function_variance", ["500060016d016d", "4f010060016c016e", function],
     2, "4107", 123, "instantiation error:"),
    ("cyclic_supertype", ["5001005f00", function],
     1, "4107", 123, "instantiation error:"),
    ("missing_supertype", ["4f01095f00", function],
     1, "4107", 123, "instantiation error:"),
]

exe = str(pathlib.Path(sys.argv[1]).resolve())
with tempfile.TemporaryDirectory() as directory:
    for name, groups, index, body, status, expected in cases:
        path = pathlib.Path(directory) / (name + ".wasm")
        path.write_bytes(module(groups, index, body))
        command = [exe, str(path)]
        if index is not None:
            command += ["-r", "main"]
        result = subprocess.run(command, capture_output=True, text=True)
        output = re.sub(r"\x1b\[[0-9;]*m", "", result.stdout + result.stderr)
        matched = expected in output.splitlines() if expected.startswith("i32.const ") else expected in output
        if result.returncode != status or not matched:
            raise AssertionError(
                f"{name}: exit {result.returncode}, expected {status}; {output!r}"
            )
print(f"GC recursive declaration binary regressions: {len(cases)}/{len(cases)}")
