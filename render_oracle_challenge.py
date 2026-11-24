#!/usr/bin/env python3
"""Render the standalone Comparator Challenge from the checked public model."""

import argparse
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
WITNESS_SIGNATURE = re.compile(
    r"(?ms)^(/-- Theorem 1\.1\. .*?-/\ntheorem twoFailureOracleBytecode :\n.*?) :="
)


def render() -> str:
    model = (ROOT / "Challenge.lean").read_text()
    proof = (ROOT / "PaperB" / "BytecodeContract.lean").read_text()
    matches = WITNESS_SIGNATURE.findall(proof)
    if len(matches) != 1:
        raise ValueError("Expected one documented theorem 1.1 declaration")
    return (
        model.rstrip() + "\n\n"
        "namespace PaperB.BytecodeContract\n\n"
        "open PaperB.OracleContract\n\n"
        + matches[0] + " := by\n  sorry\n\n"
        "end PaperB.BytecodeContract\n"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate OracleChallenge.lean")
    args = parser.parse_args()
    challenge = ROOT / "OracleChallenge.lean"
    expected = render()
    if args.write:
        challenge.write_text(expected)
    elif not challenge.is_file() or challenge.read_text() != expected:
        raise SystemExit("OracleChallenge.lean is stale. Run render_oracle_challenge.py --write.")
    else:
        print("OracleChallenge.lean matches the public model and theorem statement.")


if __name__ == "__main__":
    main()
