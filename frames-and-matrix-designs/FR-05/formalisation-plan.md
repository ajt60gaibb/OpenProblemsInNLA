# FR-05 formalisation plan

This is the historical development plan, retained with its original checkpoint
descriptions and proposed module names. As of 27 September 2026, the complete
bound and limit are locally proved; its statements below about unfinished work
are superseded by the [current source guide](lean/README.md) and
[final assembly](lean/FINAL_ASSEMBLY.md). An independent informal manuscript
audit on 8 October 2026 supports `Solved`; the isolated Linux verification
required for `Lean verified` is still pending.

## Scope and source boundary

The intended Lean result is the original FR-05 statement, strengthened to the quantitative theorem claimed as Theorem 1.4 of Zhangsong Li, [*Resolution of Vinzant's Conjecture on Phase Retrieval Injectivity*](https://zhangsong-li.github.io/injectivity_phase_retrieval.pdf), 13 September 2026:

```math
\exists C>0,\quad \forall d\ge2,\quad
\mathbb P\bigl(\operatorname{PhaseRetrievalInjective}(A_d)\bigr)\le C/d,
```

where $`A_d\in\mathbb C^{(4d-5)\times d}`$ has independent standard complex Gaussian entries. `tendsto (fun d => p_d) atTop (𝓝 0)` is then a short corollary. The Lean statement must retain the original entrywise-modulus, all-signals definition of injectivity; the stronger bound is a proof target, not a replacement problem.

The exact PDF has been archived with its SHA-256 and retrieval date in the Lean
project's source freeze. The deterministic checkpoint, a concrete
complex-Gaussian frame interface, the exact planted source law, selected
Jacobian/tail/contraction ingredients of Proposition 3.1, the source's final
conditional numerical reduction, and the exact algebraic last step of
Proposition 3.2 are now present; they remain deliberately below the full
target. The full-probability signature is recorded, unproved, in
`Challenge.lean`. Two
independent statement reviews must still approve it before any analytic module
is promoted to an advertised result. The public PDF is a live web source, so
its URL alone is not a stable statement boundary.

## The simplifying design choices

These choices reduce proof burden while preserving the target.

1. **Use the rank-two Hermitian obstruction internally, not a quotient type.** Define the public predicate directly by the original implication on `x y : Fin d → ℂ`. Prove a bridge lemma saying that an *indefinite rank-two* Hermitian `Q` with `aᵢᴴ Q aᵢ = 0` for every row produces two non-phase-equivalent signals with equal measurements. The proof only needs this forward direction. It avoids quotienting by the unit circle and avoids formalising the unnecessary reverse direction of BCMN14 Lemma 9.
2. **Represent complex matrices as finite functions.** Use `Matrix (Fin n) (Fin d) ℂ`; use `n = 4*d - 5` only under a hypothesis `2 ≤ d`. Establish the small algebraic identity `3 + 4*(d-2) = 4*d-5` once and reuse it for the chart dimension.
3. **State the main theorem with an existential constant.** Do not attempt to extract Li's unnamed absolute `C`, nor encode big-O. Each asymptotic proposition instead supplies an explicit threshold and constant; finitely many dimensions are absorbed using `p_d ≤ 1`.
4. **Keep the deterministic and measure-theoretic layers separate.** The chart, its rank/inertia facts, the contraction certificate, and the phase-retrieval obstruction are finite-dimensional algebra. Haar/Stiefel integration and Gaussian estimates belong in later files, behind precise proved lemmas—not axioms.

## Proposed project boundary

The current `frames-and-matrix-designs/FR-05/lean/` project contains the
source-frozen checkpoint and follows the repository's standard layout. It has
an explicit scaled-Gaussian frame law, proves the last algebraic implication
from the source's eventual comparison inequality to the full target, and
proves the exact second-moment-to-L² algebra used at the end of Proposition
3.2. It does not define the source likelihoods or prove their analytic
comparison estimates. The unproved full-target signature is:

```lean
theorem phaseRetrieval_injective_probability_le_inv
    : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
        phaseRetrievalProbability d ≤ C / d
```

`phaseRetrievalProbability d` is presently the outer measure of the original
all-signals predicate under that product-Gaussian law; proving the event
measurable is an outstanding obligation. A second exported theorem derives the
FR-05 limit. `Challenge.lean` exposes the exact target and remains outside the
`Solution` import boundary.

## File-by-file proof route

| File | Formal content | Source |
| --- | --- | --- |
| `Definitions.lean` | finite complex matrices, entrywise phase-retrieval predicate, Hermitian quadratic measurement map | §1, (1.1) |
| `Obstruction.lean` | an indefinite rank-two Hermitian kernel element yields a pair of unequal phase orbits with identical moduli; right-invertible coordinate changes preserve injectivity | Lemma 2.1's needed direction; §3.1 |
| `RankTwoChart.lean` | the `D(s,b), C(z,t), Qθ` chart; local invertibility of `D`; rank two and inertia `(1,1)` from the displayed factorisation | (2.4)–(2.5), (3.19) |
| `Probability.lean` | real-coordinate construction of the scaled complex-Gaussian frame law, its measurable coordinate map, and `0 ≤ p_d ≤ 1` | §3.1 |
| `Planted.lean`, `PlantedLaw.lean`, `SourceRowBridge.lean` | exact `Fε`, the planted coordinate law (3.18), and its iid-frame representation through checked rows | (3.18) |
| `FactorChart.lean`, `FactorTaylor.lean`, `Jacobian.lean`, `Newton.lean` | polynomial endpoint chart, exact Taylor/Jacobian formula (3.21), and the verified contraction-to-zero implication | (3.19), (3.21), (3.24) |
| `GaussianTail.lean`, `RadialTail.lean` | source-compatible complex-Gaussian and radial tail components of (3.22) | (3.2), (3.22) |
| `SmallBallAlgebra.lean`, `SmallBall.lean` | checked variance-profile algebra; planned row small-ball, distance-to-span, and least-singular-value tail | Lemmas 3.6–3.7 |
| `PlantedSuccess.lean` | norm event, derivative perturbation, contraction, and `P_g(E_d) ≤ C d⁻²` | Proposition 3.1 |
| `ConeKernel.lean` | cone parametrisation and the Gaussian correlation estimate | Lemma 3.3 |
| `Overlap.lean` | Haar two-frame overlap density and kernel identities/local expansion | Lemmas 3.4–3.5, (3.14)–(3.17) |
| `LikelihoodAlgebra.lean` | exact expansion from the two pairwise second-moment estimates to an eventual L² bound | final algebra in Proposition 3.2 |
| `LikelihoodComparison.lean` | source-specific likelihoods, (3.17), local/tail integrals, and the pairwise second-moment estimates | Proposition 3.2 |
| `Assembly.lean` | the final real-algebra inequality and finite-prefix absorption | (3.3)–(3.6) |
| `MainReduction.lean` | discharge of the final theorem from one explicit eventual comparison hypothesis | Theorem 1.4 |
| `Main.lean` | covariance-matched reference law, invariance, and derivation of the eventual comparison from the planted and likelihood estimates | (3.3)–(3.6), Theorem 1.4 |

The currently implemented `Definitions`, `Obstruction`, `RankTwoSeed`,
`RankTwoChart`, `FactorChart`, `FactorTaylor`, `Planted`, `PlantedTaylor`,
`Jacobian`, `Newton`, `PlantedBounds`, `PlantedLaw`, `SourceRowBridge`,
`GaussianTail`, `RadialTail`, `SmallBallAlgebra`, `Probability`, `Assembly`,
`MainReduction`, and `LikelihoodAlgebra` files form a useful kernel-checked
milestone. They formalise the exact ambiguity mechanism, the source planted
law, several quantitative inputs for Proposition 3.1, the Gaussian-law
boundary, the final numerical implication, and the last algebraic transition
in Proposition 3.2. They must still be labelled as an incomplete component,
not as a verification of FR-05.

## Proof dependencies

```text
original injectivity predicate
          │
          ├── indefinite rank-two kernel obstruction ──┐
          │                                             │
rank-two chart + quantitative contraction ─ small ball ├─ planted failure: P_g(E_d) = O(d⁻²)
                                                        │
cone correlation ─ Haar-overlap integral ─ pairwise second moments ─ checked L² algebra ───┤
                                                        │
Gaussian reference invariance + Cauchy–Schwarz ────────┴─ p_d ≤ C/d ─ limit 0
```

## Key proof obligations and checkpoints

1. **Finite-dimensional algebra.** Prove the chart factorisation exactly and derive rank/inertia with no spectral numerical computation. For the obstruction bridge, factor the rank-two indefinite form into one positive and one negative rank-one term and explicitly exhibit the two signals. This is the safest first deliverable.
2. **Quantitative inverse theorem.** Package the contraction argument as a reusable finite-dimensional lemma: if `DF 0` is invertible, its inverse norm, the Lipschitz constant of `DF`, and `‖F 0‖` meet the displayed inequalities, then `F` has a zero in the prescribed ball. This is preferable to importing a qualitative implicit-function theorem, because Li's later probability bounds need its radii.
3. **Planted-law probability.** Formalise the elementary phase and one-dimensional Gaussian small-ball bounds first, then the row-distance union bound. The claimed exponents (`κ=d⁻¹²`, failure `O(d⁻¹⁷⁄⁶)`, and `ε=d⁻⁵⁰`) leave a large safety margin for the contraction inequalities.
4. **Measure construction.** Build the product complex Gaussian as two real Gaussians of variance `1/2`; prove the polar/radial density identities once. Define the planted and reference measures by Radon–Nikodym densities and prove normalization, centering, circularity, covariance and the invertible right-multiplication representation.
5. **Correlation comparison.** Prove the cone estimate with the fixed rational parameter `η = 1/100`; use exact rational arithmetic for the numerical margin `η(1-η)/10 - 4η² > 1/2000`. Then formalise the `2 × 2` overlap density and split the eight-real-dimensional integral into the fixed local ball and exponentially small tail. This must establish the two pairwise second-moment bounds consumed by `LikelihoodAlgebra.lean`; the common quadratic term in the three kernels is essential for the `O(d⁻¹)` result.
6. **Assembly and finite cases.** Cauchy–Schwarz gives `p_d ≤ C d⁻² + sqrt(C p_d/d)`. Complete the square (or use Young's inequality) to obtain `p_d ≤ C'/d` beyond a threshold, then enlarge `C'` over the finite prefix using `0 ≤ p_d ≤ 1`.

## Main risks to settle before coding the analytic half

- The manuscript's statements use unnamed absolute constants and `O(·)`. The Lean project needs a constants-and-threshold ledger for every use; no hidden big-O notation should cross a theorem boundary.
- Haar measure on complex two-frames, the stated overlap density, and density manipulations are likely the largest Mathlib gap. Verify the pinned Mathlib API before committing to a representation. If necessary, prove the two-frame overlap formula directly by sequential sphere disintegration, exactly as Lemma 3.5 does.
- The proof has multiple informal phrases such as “sufficiently small fixed ball,” “uniformly,” and “enlarging the final constant.” Each must become a quantified radius, threshold, and constant. This is bookkeeping, not a change to FR-05.
- The claimed proof relies on the external BCMN14 criterion only for an implication that can be proved directly from the chart's indefinite form. Keeping that bridge local makes the formalisation independent of the paper's broader rank-at-most-two equivalence.

## Verification gates

After the full proof: freeze source hashes; run two fresh statement reviews and the required proof/scope/reuse reviews; use Lean 4.33.1 with the repository-pinned Mathlib/LeanCert setup; expose every advertised theorem in `Challenge.lean` and `Solution.lean`; run kernel-only LeanCert and Comparator; then reproduce the project in the required fresh non-root Linux sandbox. That full record remains required for `Lean verified`. The separate informal manuscript audit supports the catalog's `Solved` status without asserting that these formal gates have passed.
