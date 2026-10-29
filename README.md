# Online Steiner Forest in Lean

Lean 4 formalization of the tight Θ(log k · log log k) competitive ratio of greedy online Steiner forest, including the algorithm and matching upper and lower bounds.

Both bounds are proved with no `sorry` or custom axioms. The proofs use only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Statements and algorithm

- [Main theorem statements](OnlineSteinerForest/Main.lean): `OnlineSteinerForest.upper_bound` and `OnlineSteinerForest.lower_bound`, using standard mathlib finite graphs, the implemented greedy cost, and the actual offline optimum. The upper constant is uniform over tie rules; the lower instances are chosen before the tie rule.
- [Statement review](statements.md): project-defined dependencies expanded bottom-up. Only the two main proofs are replaced by `by sorry` in this documentation; the Lean sources contain their complete proofs.
- [Greedy algorithm](OnlineSteinerForest/Greedy/Algorithm.lean): purchases a minimum residual-cost path for each arriving request.
- [Shortest-path selection](OnlineSteinerForest/Graph/Paths.lean) and [offline optimum](OnlineSteinerForest/Graph/Optimum.lean).
- Bounds for independently chosen shortest paths at every arrival: [upper execution theorem](OnlineSteinerForest/UpperBound/ExecutionMain.lean) and [lower execution theorem](OnlineSteinerForest/LowerBound/ExecutionMain.lean).
- [Exact request counts](OnlineSteinerForest/LowerBound/PaddingMain.lean): the lower bound for every sufficiently large request count.
- Proof entry points: [upper bound](OnlineSteinerForest/UpperBound/Main.lean) and [lower bound](OnlineSteinerForest/LowerBound/Main.lean).

## Build and audit

Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone git@github.com:igholami/online-steiner-forest-lean.git
cd online-steiner-forest-lean
lake exe cache get
lake build
python3 scripts/check_axioms.py
```

The Lean toolchain and mathlib revision are pinned in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. Python 3 is required for the audit.

To store toolchains and downloaded mathlib caches outside the home directory, set `ELAN_HOME` and `MATHLIB_CACHE_DIR` before invoking Lean or Lake. An optional local `scripts/lean-env.sh` can hold those settings; it is ignored by Git.

The audit checks all project Lean sources for unfinished proofs and unchecked declarations, enforces a 200-line module limit, and inspects transitive axiom dependencies of every project theorem, including private helpers. It also prints the dependencies of both main bounds explicitly. See [AUDIT.txt](AUDIT.txt) and [PROOF_STATUS.txt](PROOF_STATUS.txt) for the verification record.

## Structure

- `Graph/`: paths, edge costs, feasibility, optimum, and residual metrics.
- `Greedy/`: algorithm, payments, feasibility, and basic bounds.
- `UpperBound/`: histories, auxiliary extraction, cycle-rank bounds, zones, sparse cores, forest replacement, and strided accounting.
- `LowerBound/`: ranked matching construction, sampling, bad-rank estimates, matching existence, greedy behavior, and logarithmic lower bounds.
