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
import shutil
import subprocess

from binary_wast import convert

SUITE_PIN = "b497cbb853db21be875bd5c81fcc3334168fb0b4"
ENCODER_VERSION = "wasm-tools 1.263.0 (7a2fa422c 2026-10-30)"


def prepare(suite, output, tool):
    tool = shutil.which(tool)
    if tool is None:
        raise ValueError("wasm-tools executable not found")
    suite = suite.resolve()
    output = output.resolve()
    if output == suite or suite in output.parents:
        raise ValueError("output must not be inside the source testsuite")
    sources = sorted((suite / "proposals" / "multi-memory").glob("*.wast"))
    core = sorted(suite.glob("*.wast"))
    if not core or not sources:
        raise ValueError("complete core and official multi-memory suites required")
    revision = subprocess.check_output(
        ["git", "-C", str(suite), "rev-parse", "HEAD"], text=True
    ).strip()
    version = subprocess.check_output([tool, "--version"], text=True).strip()
    if revision != SUITE_PIN or version != ENCODER_VERSION:
        raise ValueError(f"unexpected suite/encoder: {revision}; {version}")
    if len(core) != 148 or len(sources) != 48:
        raise ValueError("expected all 148 core and all 48 proposal files")
    for source in core + sources:
        pinned = subprocess.check_output([
            "git", "-C", str(suite), "show",
            f"{SUITE_PIN}:{source.relative_to(suite)}",
        ])
        if source.read_bytes() != pinned:
            raise ValueError(f"source differs from pinned revision: {source}")
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ValueError("output directory must be empty")
    replacements = {p.name for p in sources}
    manifest = []
    retained_core = []
    for source in core:
        if source.name not in replacements:
            (output / source.name).symlink_to(source)
            retained_core.append({
                "source": str(source),
                "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                "scope": "unchanged non-overlaid core script",
            })
        else:
            print(f"Official multi-memory replacement: {source.name}")
    for source in sources:
        destination = output / source.name
        coverage = convert(tool, source, destination)
        manifest.append({
            "source": str(source),
            "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "destination": str(destination),
            "scope": destination.read_text().splitlines()[1],
            "projected_sha256": hashlib.sha256(destination.read_bytes()).hexdigest(),
            **coverage,
        })
    binary_commands = sum(row["binary_scope_commands"] for row in manifest)
    exclusions = sum(len(row["text_only_malformed_lines"]) for row in manifest)
    if binary_commands != 1785 or exclusions != 88:
        raise ValueError(f"unexpected coverage: {binary_commands} commands, {exclusions} deferrals")
    (output / "provenance.json").write_text(json.dumps({
        "testsuite": revision,
        "encoder": version,
        "encoder_sha256": hashlib.sha256(Path(tool).resolve().read_bytes()).hexdigest(),
        "root_files": len(core),
        "official_files": len(sources),
        "binary_projections": manifest,
        "retained_core": retained_core,
        "proposal_binary_scope_commands": binary_commands,
        "proposal_text_only_malformed_deferred": exclusions,
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
