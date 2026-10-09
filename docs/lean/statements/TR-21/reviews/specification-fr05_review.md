# TR-21 independent pre-implementation specification review

Reviewer: `/root/fr05_review`, independent of the author of this
specification. Verdict: **APPROVE** for Lean statement implementation.
This review checks the target's meaning, not the proof of the tensor theorem.

## Reviewed files and hashes

| Input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-21/README.md` | `645fab1674f258c7d120c880118f296ab2066b25ddd257e55bd5b1ad2e84e764` |
| `docs/lean/statements/TR-21/ORIGINAL.md` | `645fab1674f258c7d120c880118f296ab2066b25ddd257e55bd5b1ad2e84e764` |
| `docs/lean/statements/TR-21/NUMERICAL_TARGETS.md` | `8f8266b6106deb2648aacc0ffc6f50801d49c076d5c4638897d5d6606a39f0f4` |
| Resolution source, `references/haidary-resolutions-2026-09-30/TR-21-Seginer-comparison-revised.tex` | `7beed83c0e2d8b9fc2b02c8203cb6d94317270044b5e14dfb9e1ecb4a1456393` |

`ORIGINAL.md` is byte-identical to the canonical README (`cmp` exit status
zero) at published base `0e916df335209819b5bf9bb8ed8f65ea978c049d`.
The registry keeps `TR-21` at
`tensor-computations/TR-21/README.md`.

## Exact statement comparison

Canonical README lines 14–41 specifies every fixed order `r ≥ 3`, every
rectangular `n₁,…,nᵣ ≥ 2`, and independent identically distributed **real**
entries with mean zero and finite first absolute moment. The law may vary
with the dimensions. `NUMERICAL_TARGETS.md` lines 9–31 keeps this entire
domain and adds no variance, density, symmetry, normalization, or moment
comparison condition. Passing to the finite product law is legitimate:
both quantities depend only on the joint law of the finite iid array.

The proposed injective norm (specification lines 33–48) is exactly the
absolute multilinear contraction optimized over one real Euclidean unit
vector in each mode, with all mode vectors varying simultaneously. The
fiber definition (lines 50–70) fixes all coordinates except the selected
mode, takes that fiber's Euclidean norm, maximizes over fibers **inside**
the expectation, and maximizes the modewise expectations **outside** it.
This is the ordering in canonical README lines 18–31 and in the manuscript's
equations (1)–(2), source lines 56–72. Finite first moment suffices to make
all expectations finite because each relevant norm is bounded by the sum
of absolute values of the finitely many entries.

Canonical README lines 33–39 asks for `∀ r ≥ 3, ∃ 0 < cᵣ ≤ Cᵣ`, with those
constants selected before the format and distribution, such that
`cᵣ F(T) ≤ E inj(T) ≤ Cᵣ F(T)` uniformly. The specification lines 72–87
preserves precisely that order and both inequalities. The revised
manuscript's Theorem 1.1, source lines 73–83, proves the stronger
lower coefficient `1` and an order-only upper constant. The specification
lines 89–101 correctly records this as a separate companion target, while
retaining the original existential comparison. The source's full-law
completion, lines 466–570, explicitly removes symmetry and finite-variance
restrictions, so neither can be inserted into the public Lean target.

There is no fixed decimal constant to encode. The zero law, all aspect
ratios, and dimension-dependent heavy-tailed or sparse laws remain included.
The `r = 2` matrix predecessor and Bernoulli corollary are not substitutes
for the stated `r ≥ 3` uniform theorem. I found no mathematical or
numerical mismatch and no pre-implementation blocker.
