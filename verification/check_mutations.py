#!/usr/bin/env python3
"""Negative proof tests. Each valid-syntax mutation must fail in step_balance."""
from pathlib import Path
import re
import subprocess
import sys

lean = Path(sys.argv[1]).resolve()
root = Path(__file__).resolve().parent
source = (root / "ResourcePrefix.lean").read_text(encoding="utf-8")
anchor = "/-- Derived from concrete execution rules; balance is not a premise. -/"
assert source.count(anchor) == 1
out = root / "mutations"
out.mkdir(exist_ok=True)
mutations = {
    "counterfeit_copy": "  | counterfeit (k : Nat) :\n      Step (.run .copyNat (.token k)) .quiet\n        (.done (.pair (.token k) (.token k)))\n\n",
    "silent_drop": "  | silentDrop (k : Nat) :\n      Step (.run .release (.token k)) .quiet (.done .unit)\n\n",
}
reports = []
for name, rule in mutations.items():
    text = source.replace(anchor, rule + anchor)
    path = out / f"{name}.lean"
    path.write_text(text, encoding="utf-8")
    result = subprocess.run([str(lean), str(path)], capture_output=True, text=True, timeout=60)
    log = result.stdout + result.stderr
    (out / f"{name}.log").write_text(log, encoding="utf-8")
    first = text[:text.index("theorem step_balance")].count("\n") + 1
    last = text[:text.index("inductive Prefix")].count("\n") + 1
    errors = [int(n) for n in re.findall(r"\.lean:(\d+):\d+: error:", log)]
    if result.returncode == 0 or not any(first <= n < last for n in errors):
        raise SystemExit(f"Mutation did not fail in the intended conservation proof: {name}\n{log}")
    reports.append(f"{name}: rejected in step_balance; exit={result.returncode}")
(root / "mutation-status.txt").write_text("\n".join(reports) + "\n", encoding="utf-8")
print("\n".join(reports))
