# MD-02 resolution submission — Shanmu Jin, 22 November 2026

[*The sharp Lovász theta constant for two random graph models*](manuscript.pdf),
Theorem 1, model (2) (p. 1), and Section 3 (pp. 7–14), give an affirmative
answer to the [original MD-02 target](../../matrix-discrepancy-and-optimization/MD-02/README.md).
The result is the expectation limit over every order, including even orders
with a singleton antipodal distance class. [Chen et al., Theorem 1.1](https://arxiv.org/abs/2610.22971v1)
establish the odd-order limit, including composite odd orders.

Shanmu Jin is affiliated with the Department of Neurosurgery, Peking Union
Medical College Hospital. The manuscript credits automated proof discovery
to GPT-6.2 Sol Max in Codex. The author reorganized the resulting material
and takes full responsibility for the work.

[Manuscript source](manuscript.tex) ·
[Published manuscript and Lean project at the immutable revision](https://github.com/jinshanmu/LovaszTheta/tree/79d3682466a040230b751f3c8cf588fe75d7e46e) ·
[Catalog statement check](verification/MD02Check.lean) ·
[Dated verification log](verification/2026-11-22.txt)

## Reproduce the Lean check

The proof project pins Lean v4.36.0 and mathlib v4.36.0 at
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The other dependencies are pinned in
its [Lake manifest](https://github.com/jinshanmu/LovaszTheta/blob/79d3682466a040230b751f3c8cf588fe75d7e46e/Lean/lake-manifest.json).
Run these commands from the root of the catalog checkout with Elan installed.

```bash
md02_check_file="$PWD/references/jin-md02-2026-11-22/verification/MD02Check.lean"
git clone https://github.com/jinshanmu/LovaszTheta.git md02-proof
git -C md02-proof checkout --detach 79d3682466a040230b751f3c8cf588fe75d7e46e
cd md02-proof/Lean
lake exe cache get
lake build --wfail
lake lint --wfail
lake env lean --root="$(dirname "$md02_check_file")" -DwarningAsError=true "$md02_check_file"
```

The check matches the selected inversion classes, the real SDP maximum and
the fair expectation to the published proof. It proves the catalog limit
through the sequence of orders starting at two and enforces the standard
axiom allowlist for the limit and five related declarations. The submitter
reran the proof build, linter and statement check on Linux from a fresh
public clone with cached dependencies at the pinned revisions.
Independent catalog review is pending.
