#!/usr/bin/env python3
"""Run every certificate used by the Erdős 1038 manuscript."""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LOGS = ROOT / "logs"
LOGS.mkdir(exist_ok=True)

COMMANDS = [
    ("contact_existence", [sys.executable, str(ROOT / "contact_existence.py")]),
    ("forcing", [sys.executable, str(ROOT / "erdos1038_forcing_exact.py")]),
    (
        "endpoint",
        [
            sys.executable,
            str(ROOT / "erdos1038_exact_endpoint_certificate.py"),
            "--workers",
            "1",
        ],
    ),
    ("symbolic_endpoint", [sys.executable, str(ROOT / "symbolic_endpoint_verifier.py")]),
    ("symbolic_contact", [sys.executable, str(ROOT / "symbolic_contact_verifier.py")]),
]


def main() -> None:
    env = os.environ.copy()
    env.setdefault("ERDOS1038_ARB_BITS", "384")
    env.setdefault("ERDOS1038_PHI_TERMS", "50")

    for name, command in COMMANDS:
        print(f"=== {name} ===", flush=True)
        result = subprocess.run(
            command,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        print(result.stdout, end="")
        (LOGS / f"{name}.log").write_text(result.stdout)
        if result.returncode:
            raise SystemExit(f"{name} failed with exit status {result.returncode}")

    print("PASS: all certificates")


if __name__ == "__main__":
    main()
