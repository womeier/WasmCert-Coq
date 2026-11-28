#!/usr/bin/env python3
"""Run every projected final-EH command; retain failures and infrastructure errors."""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import subprocess


def run(directory, executable):
    manifest = json.loads((directory / "provenance.json").read_text())
    totals, results, infrastructure = collections.Counter(), [], []
    for entry in manifest["files"]:
        projection = Path(entry["projection"])
        report_file = projection.parent / "results.json"
        process = None
        try:
            source_hash = hashlib.sha256(Path(entry["source"]).read_bytes()).hexdigest()
            if source_hash != entry["sha256"]:
                raise ValueError("source file changed since projection")
            document = json.loads(projection.read_text())
            if [c["provenance"] for c in document["commands"]] != entry["mapping"]:
                raise ValueError("projection/source mapping changed")
            for command in document["commands"]:
                if "filename" in command:
                    binary = projection.parent / command["filename"]
                    digest = hashlib.sha256(binary.read_bytes()).hexdigest()
                    if digest != command["provenance"]["binary_sha256"]:
                        raise ValueError("encoded module changed since projection")
            process = subprocess.run([str(executable), str(projection)],
                                     capture_output=True, text=True, timeout=600)
            report = json.loads(process.stdout)
            commands = report["commands"]
            if (report["total"] != entry["binary_scope_commands"] or
                    len(commands) != report["total"] or
                    [c["provenance"] for c in commands] != entry["mapping"] or
                    [c["type"] for c in commands] != [m["type"] for m in entry["mapping"]] or
                    report["passed"] != sum(c["passed"] is True for c in commands) or
                    process.returncode != (0 if report["passed"] == report["total"] else 1)):
                raise ValueError("inconsistent result accounting/provenance/exit status")
            report_file.write_text(json.dumps(report, indent=2) + "\n")
            for command in commands:
                kind = command["type"]
                totals[kind + ":total"] += 1
                if command["passed"]:
                    totals[kind + ":passed"] += 1
            print(f"{projection.parent.name}: {report['passed']}/{report['total']}")
            results.append(report)
        except (ValueError, KeyError, TypeError, OSError, subprocess.TimeoutExpired) as error:
            infrastructure.append({"source": entry["source"], "error": str(error),
                                   "stdout": process.stdout if process else "",
                                   "stderr": process.stderr if process else "",
                                   "exit": process.returncode if process else None})
            print(f"{projection.parent.name}: INFRASTRUCTURE ERROR: {error}")
    summary = {"testsuite": manifest["testsuite"], "encoder": manifest["encoder"],
               "runtime_executable_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
               "passed": sum(r["passed"] for r in results),
               "total": sum(r["total"] for r in results),
               "required_binary_scope_commands": sum(
                   e["binary_scope_commands"] for e in manifest["files"]),
               "deferred_text_only_malformed": sum(
                   len(e["deferred_text_only_malformed"]) for e in manifest["files"]),
               "by_command_type": dict(totals), "infrastructure_errors": infrastructure}
    (directory / "results.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    return not infrastructure and summary["passed"] == summary["required_binary_scope_commands"]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("projection", type=Path)
    parser.add_argument("--executable", type=Path,
                        default=Path("_build/default/tests/eh_script/eh_script.exe"))
    args = parser.parse_args()
    raise SystemExit(0 if run(args.projection, args.executable.resolve()) else 1)
