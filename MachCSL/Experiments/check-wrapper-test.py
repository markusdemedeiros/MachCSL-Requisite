#!/usr/bin/env python3
"""Check exit-status handling with fake services; never start Lean or systemd."""
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
NORMAL = "Main processes terminated with: code=exited, status=0/SUCCESS"
KILLED = "Main processes terminated with: code=killed, status=15/TERM"


def main():
    cases = [
        ("normal", [NORMAL], 0, 0),
        ("stopped despite unit success", [KILLED], 0, 1),
        ("service failure", [], 7, 7),
        ("missing termination record", [], 0, 1),
        ("last termination record wins", [NORMAL, KILLED], 0, 1),
    ]
    with tempfile.TemporaryDirectory(prefix="req-checker-test-") as directory:
        bin_dir = Path(directory)
        # No compiler runs in these tests, so taking the real compiler lock
        # would unnecessarily block other focused checks.
        for name, body in [("lake", "exit 99"), ("flock", "exit 0")]:
            path = bin_dir / name
            path.write_text("#!/bin/sh\n" + body + "\n")
            path.chmod(0o700)
        fake = bin_dir / "systemd-run"
        env = {**os.environ, "PATH": directory + os.pathsep + os.environ["PATH"]}
        for name, lines, service_exit, expected in cases:
            # All mocked output is constant test data, not shell input.
            fake.write_text("#!/bin/sh\n" + "".join(f"echo '{line}'\n" for line in lines)
                            + f"exit {service_exit}\n")
            fake.chmod(0o700)
            result = subprocess.run(["bash", "Experiments/check.sh", "ignored.lean"],
                                    cwd=ROOT, env=env, capture_output=True, text=True)
            assert result.returncode == expected, (name, result.returncode,
                                                    result.stdout, result.stderr)
            print(name + ": PASS")


if __name__ == "__main__":
    main()
