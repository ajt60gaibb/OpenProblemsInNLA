# MF-13 resolution submission — Shanmu Jin, 21 November 2026

[*Symmetric maximizers of Lyapunov operators*](manuscript.pdf), Theorem 1 (p. 1)
and the order-six proof in Section 3 (pp. 2–4), claims an affirmative resolution
of the [original MF-13 target](../../matrix-functions-and-stability/MF-13/README.md).
The author is Shanmu Jin, Department of Neurosurgery, Peking Union Medical
College Hospital. The manuscript credits automated proof discovery to GPT-6.2
Sol at the `max` reasoning setting in Codex. The author reorganized the work
and takes full responsibility for it.

[Manuscript source](manuscript.tex) · [Published source and Lean proof at the immutable revision](https://github.com/jinshanmu/SymmetricMaximizer/tree/9a1cedcf3bec473a322b45d770bedeac7050dbb9) · [Exact target check](verification/MF13Check.lean) · [Dated verification log](verification/2026-11-21.txt)

## Reproduce the Lean check

The published project pins Lean v4.36.0 and mathlib v4.36.0 at
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The rest of its dependency
revisions are in the [locked manifest](https://github.com/jinshanmu/SymmetricMaximizer/blob/9a1cedcf3bec473a322b45d770bedeac7050dbb9/Lean/lake-manifest.json).

Run from the root of the catalog checkout with Elan installed:

```bash
mf13_check_file="$PWD/references/jin-mf13-2026-11-21/verification/MF13Check.lean"
git clone https://github.com/jinshanmu/SymmetricMaximizer.git mf13-proof
git -C mf13-proof checkout --detach 9a1cedcf3bec473a322b45d770bedeac7050dbb9
cd mf13-proof/Lean
lake exe cache get
lake build --wfail
lake lint --wfail
lake env lean -DwarningAsError=true "$mf13_check_file"
```

The check proves the trace formula for the Frobenius norm, the existence of a
common greatest value, and equality of the two suprema. It also enforces the
axiom allowlist for those declarations and the three imported main results.
The submitter reran the verification on Linux from a fresh clone of the
published proof using cached dependencies at the locked revisions.
Independent catalog review of the submission is pending.
