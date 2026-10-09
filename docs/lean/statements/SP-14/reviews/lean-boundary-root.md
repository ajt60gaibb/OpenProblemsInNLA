# SP-14 independent Lean boundary review

**Reviewer:** `/root` (AI agent), 9 October 2026. **Verdict:** APPROVE the exact statement boundary. I did not write the Lean statement; author is `/root/next_solved_triage`. This approval concerns statement fidelity, not a Lean proof of the negative target.

I read the live and frozen Lean files, the full canonical `README.md` statement, and the approved numerical contract. `Circle.exp t` is definitionally `Complex.exp (t * I)` in the pinned Mathlib, so the real interval `0..2π` integrand uses precisely `a(e^{it}) exp(-ikt)` for every integer `k`. The `Fin n` matrix entry uses row minus column, without conjugation or wraparound. The complex characteristic polynomial's `.roots` is a multiset, and mapping `F` then summing preserves algebraic multiplicity; the empirical divisor is the actual `n`. The `n=0` convention is harmless to the `atTop` limit.

The inner and outer extension predicates existentially quantify actual complex functions, require complex differentiability on their respective open annuli, continuity through the unit-circle side, and equality to the boundary symbol. The opposite radius carries no boundary condition. `OriginalConjecture` quantifies every continuous symbol with neither extension and every continuous compactly supported complex test, then asserts the full natural-order `Tendsto` to the normalized canonical integral. `Target` is literally its negation. There is no imported witness axiom, arbitrary extension flag, narrowed class, or finite-order proxy. The live and frozen bodies differ only by the frozen comment and namespace replacement. LeanCert kernel assertion lines are statement checks; they do not establish `Target`.

I compared the statement's import closure and pins, and found no numerical construction parameters embedded as new target hypotheses. The separate source witness, including `θ=2^(-10000)`, remains a future proof obligation. In particular, this boundary cannot accidentally certify the source manuscript's finite `θ/2` shorthand as a theorem.

## Bound inputs (SHA-256)

| Input | SHA-256 |
| --- | --- |
| `eigenvalues-and-inverse-problems/SP-14/README.md` and `docs/lean/statements/SP-14/ORIGINAL.md` | `9d0c6376080838ea50e8736cb4249276c06a528479fb9c9f565cc7747a485075` |
| `docs/lean/statements/SP-14/NUMERICAL_TARGETS.md` | `f507ad236fc7c9e9547ce23ebe74ddffac84872d66648cc8b543ff89d6f39efc` |
| `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `lean-statements/Reviewed/SP14.lean` | `bff729881ee4591e73290e57fb1910e15b3cb3421044e5cdc1a3e5b44e1e5c52` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
