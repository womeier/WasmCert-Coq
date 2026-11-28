#!/usr/bin/env python3
"""Prepare the complete versioned core + official multi-memory binary profile.

Root expectations are not modified. Official same-name proposal files replace
their root versions explicitly; all other core files remain in the run.
Only text-only malformed assertions are outside this non-text profile, and
their exact source lines are reported by binary_wast and in the manifest.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from binary_wast import convert


def prepare(suite, output, tool):
    suite = suite.resolve()
    output = output.resolve()
    if output == suite or suite in output.parents:
        raise ValueError("output must not be inside the source testsuite")
    sources = sorted((suite / "proposals" / "multi-memory").glob("*.wast"))
    core = sorted(suite.glob("*.wast"))
    if not core or not sources:
        raise ValueError("complete core and official multi-memory suites required")
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ValueError("output directory must be empty")
    replacements = {p.name for p in sources}
    manifest = []
    for source in core:
        if source.name not in replacements:
            (output / source.name).symlink_to(source)
        else:
            print(f"Official multi-memory replacement: {source.name}")
    for source in sources:
        destination = output / source.name
        convert(tool, source, destination)
        manifest.append({
            "source": str(source),
            "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "destination": str(destination),
            "scope": destination.read_text().splitlines()[1],
        })
    revision = subprocess.check_output(
        ["git", "-C", str(suite), "rev-parse", "HEAD"], text=True
    ).strip()
    version = subprocess.check_output([tool, "--version"], text=True).strip()
    (output / "provenance.json").write_text(json.dumps({
        "testsuite": revision,
        "encoder": version,
        "root_files": len(core),
        "official_files": len(sources),
        "binary_projections": manifest,
    }, indent=2) + "\n")
    print(f"Suite revision: {revision}; encoder: {version}")
    print(f"Prepared {len(list(output.glob('*.wast')))} files; "
          "run the entire output directory with run_wast.sh")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite", type=Path, default=Path("wast_testsuite"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--wasm-tools", default="wasm-tools")
    args = parser.parse_args()
    prepare(args.suite, args.output, args.wasm_tools)
