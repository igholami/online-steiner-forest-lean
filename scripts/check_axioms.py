#!/usr/bin/env python3
"""Check theorem dependencies and keep individual Lean modules short."""
import pathlib
import re
import subprocess
import tempfile

root = pathlib.Path(__file__).resolve().parent.parent
sources = [root / "OnlineSteinerForest.lean",
           *sorted((root / "OnlineSteinerForest").rglob("*.lean"))]
modules = []
for path in sources:
    source = path.read_text()
    if len(source.splitlines()) > 200:
        raise SystemExit(f"Module exceeds 200 lines: {path.relative_to(root)}")
    if re.search(r"\b(sorry|admit|sorryAx)\b|^\s*(axiom|unsafe)\b", source, re.M):
        raise SystemExit(f"Unfinished proof or unchecked declaration in {path}")
    modules.append(".".join(path.relative_to(root).with_suffix("").parts))

with tempfile.TemporaryDirectory(prefix="online-lean-audit-") as directory:
    audit = pathlib.Path(directory) / "Audit.lean"
    # Inspect elaborated declarations, including private and nested namespaces.
    # Source-name extraction misses precisely those helper proofs.
    audit.write_text("\n".join(f"import {module}" for module in modules) + r'''
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let s := name.toString
    if s.startsWith "OnlineSteinerForest." || s.startsWith "_private.OnlineSteinerForest." then
      if info.isTheorem then
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unexpected axiom {ax} in {name}"
        count := count + 1
  logInfo m!"Audited {count} project theorems: only standard axioms."
#print axioms OnlineSteinerForest.upper_bound
#print axioms OnlineSteinerForest.lower_bound
#print axioms OnlineSteinerForest.execution_upper_bound
#print axioms OnlineSteinerForest.execution_lower_bound
#print axioms OnlineSteinerForest.greedy_lower_bound_exact_count
''')
    result = subprocess.run(["lake", "env", "lean", str(audit)], cwd=root,
                            text=True, capture_output=True)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    print(result.stdout, end="")
    print(f"Checked {len(sources)} modules, including private helper theorems.")
    print("Only propext, Classical.choice, and Quot.sound are allowed.")
