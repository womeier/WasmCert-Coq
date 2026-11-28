"""Contextual source type scope through the actual binary validation path.

Module definitions validate without linking/instantiating imports. Invalid
indices are format-valid, and must never be reported as malformed bytes.
"""
import pathlib
import re
import subprocess
import sys
import tempfile


def section(tag, payload):
    assert len(payload) < 128
    return bytes([tag, len(payload)]) + payload


def module(types="01600000", *, imports=None, tables=None, globals=None,
           elements=None, locals=None, body=None):
    data = bytes.fromhex("0061736d01000000") + section(1, bytes.fromhex(types))
    for tag, value in [(2, imports), (3, "0100" if body is not None else None),
                       (4, tables), (6, globals), (9, elements)]:
        if value is not None:
            data += section(tag, bytes.fromhex(value))
    if body is not None:
        code = bytes.fromhex(locals or "00") + bytes.fromhex(body) + b"\x0b"
        assert len(code) < 128
        data += section(10, bytes([1, len(code)]) + code)
    return data


cases = [
    ("table_index_in_scope", module(tables="0163000000"), True),
    ("table_index_out_of_scope", module(tables="0163010000"), False),
    ("table_source_alias_canonical_name",
     module("02600000600000", tables="0163010000"), True),
    ("table64_index_in_scope", module(tables="0163000400"), True),
    ("table64_index_out_of_scope", module(tables="0163010400"), False),
    ("table_struct_heap_in_scope", module("015f00", tables="0163000000"), True),
    ("table_nonnull_needs_initializer", module(tables="0164000000"), False),
    ("table_abstract_nonnull_initializer",
     module(tables="01400064700000d2000b", body=""), True),
    ("table_abstract_nonnull_rejects_null",
     module(tables="01400064700000d0700b"), False),
    ("table_indexed_nonnull_from_import",
     module(imports="01016d016703640000", tables="0140006400000023000b"), True),
    ("table_indexed_nullable_cannot_initialize_nonnull",
     module(imports="01016d016703630000", tables="0140006400000023000b"), False),
    ("import_table_index_in_scope", module(imports="01016d01740163000000"), True),
    ("import_table_index_out_of_scope", module(imports="01016d01740163010000"), False),
    ("import_global_index_in_scope", module(imports="01016d016703630000"), True),
    ("import_global_index_out_of_scope", module(imports="01016d016703630100"), False),
    ("global_index_in_scope",
     module(imports="01016d016703630000", globals="0163000023000b"), True),
    ("global_index_out_of_scope",
     module(imports="01016d016703630000", globals="0163010023000b"), False),
    ("element_index_in_scope", module(elements="0105630000"), True),
    ("element_index_out_of_scope", module(elements="0105630100"), False),
    ("local_nullable_index_in_scope", module(locals="01016300", body=""), True),
    ("local_index_out_of_scope", module(locals="01016301", body=""), False),
    ("local_nonnull_not_defaultable", module(locals="01016400", body=""), False),
    ("dead_block_function_kind", module(body="0002000b"), True),
    ("dead_block_unknown_index", module(body="0002010b"), False),
    ("dead_block_struct_kind", module("026000005f00", body="0002010b"), False),
    ("dead_indirect_function_kind",
     module(tables="01700000", body="00110000"), True),
    ("dead_indirect_unknown_index",
     module(tables="01700000", body="00110100"), False),
    ("dead_indirect_struct_kind",
     module("026000005f00", tables="01700000", body="00110100"), False),
    ("import_function_kind", module(imports="01016d01660000"), True),
    ("import_function_source_alias",
     module("02600000600000", imports="01016d01660001"), True),
    ("import_function_not_struct", module("015f00", imports="01016d01660000"), False),
]

exe = str(pathlib.Path(sys.argv[1]).resolve())
with tempfile.TemporaryDirectory() as directory:
    for name, data, valid in cases:
        encoded = "".join(f"\\{byte:02x}" for byte in data)
        path = pathlib.Path(directory) / (name + ".wast")
        path.write_text(f'(module definition binary "{encoded}")\n')
        result = subprocess.run([exe, "--stage", "--wast", str(path)],
                                capture_output=True, text=True)
        output = re.sub(r"\x1b\[[0-9;]*m", "", result.stdout + result.stderr)
        expected = "Result: 1/1" if valid else "Result: 0/1"
        if result.returncode != 0 or expected not in output:
            raise AssertionError(f"{name}: expected {expected}; {output!r}")
        if "error in parsing module" in output or "PARSE ERROR:" in output:
            raise AssertionError(f"{name}: source-scope validation became a parser exclusion")
print(f"contextual source scope binary regressions: {len(cases)}/{len(cases)}")
