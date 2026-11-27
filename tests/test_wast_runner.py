"""Regression: a passing file must never mask a broken sibling."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile


runner = str(Path(sys.argv[1]).resolve())
with tempfile.TemporaryDirectory() as directory:
    root = Path(directory)
    (root / "pass.wast").touch()
    (root / "broken.wast").touch()
    exe = root / "interpreter"
    for bad, status in [
        ("exit 1", 1),
        ("echo 'no summary'", 1),
        ("echo 'Result: broken'", 1),
        ("echo 'Result: 0/0'", 1),
        ("echo 'Result: 2/1'", 1),
        ("echo 'Result: 0/1'", 1),
        ("echo 'Result: 1/1'", 0),
    ]:
        exe.write_text(
            "#!/bin/bash\n"
            'case "$2" in\n'
            '  */pass.wast) echo "Result: 1/1";;\n'
            f"  *) {bad};;\n"
            "esac\n"
        )
        exe.chmod(0o755)
        result = subprocess.run(
            ["bash", runner, str(root)],
            env={**os.environ, "EXE": str(exe), "JOBS": "2"},
            capture_output=True, text=True,
        )
        if result.returncode != status:
            raise AssertionError((bad, result.returncode, result.stdout, result.stderr))
print("7/7 WAST runner regressions passed")
