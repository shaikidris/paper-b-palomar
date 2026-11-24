# Reachability After Two Vertex Failures in DAGs

This Lean 4 package formalizes Theorem 1.1 of *Near-Linear Preprocessing
for Reachability After Two Vertex Failures in Directed Acyclic Graphs*.
The theorem fixes a deterministic word-RAM builder and a query program for
a DAG with `n` vertices, `m` arc occurrences, and a specified source.
With `L = ⌈log₂(n+2)⌉`, construction uses `O((n+m)L²)` operations and
`O(n+m)` peak words. The retained index uses `O(n)` words. A query uses
only that index, an original target, and a list of at most two failed
vertices. It decides reachability in `O(L)` operations. [Paper v1.3](https://doi.org/10.5281/zenodo.24350515)

The selected declaration is
`PaperB.BytecodeContract.twoFailureOracleBytecode`. The
[oracle challenge](OracleChallenge.lean) exposes the instruction semantics
and the build and query observations. The [proof entrypoint](Solution.lean)
also exports the v1.2 bounds for the same machine implementation.

```sh
lake build Solution
python3 -B render_oracle_challenge.py
lake build OracleChallenge
lake env lean Audit.lean
```

The deliberate proof hole in `OracleChallenge.lean` belongs to the
Comparator's statement input. The proof build uses `Solution` and its
imports. The [Comparator configuration](comparator.json) selects the
bytecode theorem and lists the allowed Lean axioms.
