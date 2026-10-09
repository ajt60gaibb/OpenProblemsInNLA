# FR-10 independent specification review

**Decision: APPROVE** for Lean statement implementation. This is a review of
the mathematical target, not a proof or a Lean verification result.

## Reviewed inputs

| Input | SHA-256 |
| --- | --- |
| `frames-and-matrix-designs/FR-10/README.md` | `6e7f8ddb900da1cef486a6196c3ac277e79c7d0c953099b0e27441efea569e44` |
| `docs/lean/statements/FR-10/ORIGINAL.md` | `6e7f8ddb900da1cef486a6196c3ac277e79c7d0c953099b0e27441efea569e44` |
| `docs/lean/statements/FR-10/NUMERICAL_TARGETS.md` | `4302bb580024b66b0bdc7e65e493eefdba2ae33659c7181757f5965aea85cad3` |

The canonical README at published base `0e916df335209819b5bf9bb8ed8f65ea978c049d`
is byte-identical to `ORIGINAL.md` (`cmp` exit status 0). I also checked the
resolution's revised LaTeX source,
`references/haidary-resolutions-2026-09-30/Walsh_RIP_with_replacement_revised.tex`
(SHA-256 `634946e8576c0c7f41fda7e18e2e5f55e6aec9dbaaaf8aaffc2018ca7b84d22e`).

## Statement comparison

- Canonical README lines 13–32 and manuscript lines 58–80 agree on
  `d ≥ 1`, `N = 2^d`, Walsh rows and columns indexed by `𝔽₂^d`, ordered
  independent uniform draws with replacement, all real vectors of support
  size at most `k`, weak distortion bounds `1/2` and `3/2`, inclusive
  success threshold `0.9`, and the minimum over **positive** sample counts.
  `NUMERICAL_TARGETS.md` lines 8–35 preserves each of these features.
- Its squared-energy formula is exactly the canonical sampled matrix formula:
  `sqrt(N/m) * N^(-1/2) = 1/sqrt(m)` for `m ≥ 1`, hence the squared norm is
  `(1/m) * ∑ᵢ (∑ᵦ (-1)^(aᵢ·b) xᵦ)^2`. This is a valid algebraic simplification,
  including repeated rows. There are `N^m` ordered samples, so finite
  uniform counting gives the exact independent-draw probability.
- Canonical README lines 38–46 and manuscript Theorem 1.1, lines 83–93,
  agree on `m_*(N,1) = 1` and a **single pair** of universal positive
  constants for every `d ≥ 1` and `2 ≤ k ≤ 2^d`. The logarithms are natural
  (manuscript line 58). The manuscript further permits `c = 1/2000`.
  `NUMERICAL_TARGETS.md` lines 37–51 includes the uniform order statement
  and explicitly records this stronger coefficient.

## Implementation requirements

The public Lean event must quantify over all eligible vectors for one fixed
sample. It must allow `m > N`, repeated rows, `k = N`, and `d = 1, k = 2`.
Use an exact rational threshold `9/10`; avoid floating-point numerals.
The definition of `mStar` must be accompanied by nonemptiness and least-element
properties: `Nat.sInf ∅ = 0` would not represent the stated minimum. No
monotonicity in `m` is supplied or needed for the definition.

The existential-constant order result is the original problem's resolved
target. If the Lean artifact advertises the **full numerical strength** of
the manuscript's Theorem 1.1, it should additionally expose the lower bound
with coefficient `1/2000`; the specification already identifies that claim.
The historical Colbrook numerical limits in README lines 52–59 are subsidiary
results and do not replace the uniform FR-10 theorem.
