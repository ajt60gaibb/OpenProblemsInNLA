# SP-14 independent pre-statement review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE the exact mathematical and numerical **design contract** in `STATEMENT_REVIEW.md` for implementing a Lean statement, with the finite-fraction/liminf correction below binding on implementation. This is not a Lean statement, proof of the counterexample, or certification of the preserved 2,118-line analytic argument.

## Original target and formal boundary

The permanent registry maps `SP-14` to `eigenvalues-and-inverse-problems/SP-14/README.md`; the complete original conjecture remains in that page's `## Statement`. Its Fourier coefficient is exactly `(1/(2π))∫₀²π a(e^{it})e^{−ikt}dt` for **every integer** `k`, and its Toeplitz entry is `a_(row−column)` for rows and columns `0,…,n−1`. The review preserves this sign, normalization, actual finite Toeplitz matrix, and absence of a normality or circulant assumption. The source manuscript uses the same convention in its opening notation.

The original hypotheses are that a **continuous complex-valued** symbol on the unit circle has neither a holomorphic extension from an **inner** annulus `r<|z|<1` (some `0<r<1`) nor from an **outer** annulus `1<|z|<R` (some `R>1`), with continuous boundary values equal to the symbol at `|z|=1`. The reviewed contract's suggested `DifferentiableOn ℂ` on the open annulus and `ContinuousOn` through only the unit-circle side encode this boundary correctly; no condition is needed at the opposite radius. The absence of **both** extensions is conjunctive. There is no Jordan-curve or winding-number premise. Actual extension functions must be quantified; an uninterpreted flag or unproved Fourier-decay surrogate would change the target.

For every such symbol and **every** continuous compactly supported complex test `F`, the conjecture asserts a full-sequence complex limit of the empirical average to the circle integral. The empirical sum must use the characteristic polynomial's complex root **multiset**, so a root of algebraic multiplicity `h` contributes `h` copies even for a nondiagonalizable matrix. Division is by the actual positive matrix order `n`. The suggested `OriginalConjecture` quantifier order and `Target := ¬ OriginalConjecture` retain the complete one-way original assertion. A particular symbol, test and subsequence can refute that limit, but a Jordan-class restriction, one-vector test, alternative matrix sequence, or convergence only along a subsequence would not encode it.

## Source witness and exact numerical scope

The preserved Theorem 6.1 supplies one continuous symbol with neither extension and selected odd orders `n_j=2m_j+1` with both `+1` and `−1` as eigenvalues of algebraic multiplicity at least `⌊θm_j⌋`, where **`θ=2^(−10000)`**. The review preserves both eigenvalues, their algebraic multiplicities, and their exclusion from the symbol range. Its proposed stronger witness also retains the source proof's strictly increasing orders, and it proposes a quantitative separation from `+1`, which is needed for the explicit test. The base identity `charpoly(T_(2m+1)(a₀))(w)=w(w²−1)^m` matches the manuscript, but the base symbol has an outer extension and must not be substituted for the final counterexample. The square root in `a₀(z)=z√(1+z^(−2))` is the source's branch analytic outside the unit circle and equal to one at infinity, not an unspecified principal branch.

The exact construction numbers in the review match the manuscript: `γ=2^(−1000)`, `θ=2^(−10000)`, `σ=3/8`, `m₀=2^10000`, `κ=2^(−1010)`, `β_j=γ2^(−j−4)`, `q_j=3m_j/8`, `h_j=⌊θm_j⌋`, and packet scale `τ_j=κ2^(−⌈√(2m_(j−1)+1)⌉)`. The selected `m_j` are divisible by eight and at least eight times the preceding order. These huge constants are construction data, not extra hypotheses in `OriginalConjecture`; keeping the powers symbolic is faithful. The source's positive Fourier packets rule out the **outer** extension, while untouched negative binomial coefficients rule out the **inner** extension, consistent with the Fourier sign convention.

The real tent test `φ(w)=max(0,1−8|w−1|)` is continuous, nonnegative, equals one at `+1`, and has compact support inside the closed `1/8` ball around `+1`; its complex coercion `Φ` is an admissible original test. The source proves `dist(1,a₀(𝕋))=√2−1` and `‖a−a₀‖∞<2γ`, so `dist(1,a(𝕋))≥√2−1−2γ>1/8`. This **quantitative** margin gives `Φ(a(z))=0` at every circle point and hence canonical average zero. Mere nonmembership `1∉a(𝕋)` would not prove that conclusion for this fixed `Φ`. The `−1` multiplicity is retained as part of the stronger source theorem, although this particular tent test needs only the `+1` multiplicity.

At a selected finite order the justified lower bound is exactly

```text
EmpiricalRealAverage(a,φ,2m_j+1) ≥ ⌊θm_j⌋/(2m_j+1).
```

Since `m_j→∞`, the right side tends to `θ/2>0`, giving `liminf_j EmpiricalRealAverage≥θ/2`; a full-sequence complex limit to zero is impossible. The fraction itself is strictly below `θ/2` for every finite positive `m_j`. The canonical README, generated `problem.tex`, and submission summary use the shorthand that the empirical average is “at least `θ/2` along” the selected orders. The source proof establishes the finite fraction and its **limit**, not a pointwise `θ/2` lower bound on every selected empirical average. The pre-statement review correctly identifies this distinction. The Lean witness and contradiction must use the exact finite fraction and limit/liminf, not import the shorthand as a theorem.

## Review boundary

No `NLA.Statements.SP14.Target` or SP-14 Lean proof exists at this review. The source's separate informal AI audit reports PASS but expressly did not recompute the constant ledger or reprove two central analytic propositions line by line; I did not certify those steps here. The verdict approves statement fidelity and a route for a later source-witness theorem, not feasibility or proof truth. A future Lean development must prove real one-sided extension semantics, all multiplicity and separation facts, the subsequential contradiction, and finally the literal negation of the original universal proposition in LeanCert kernel mode.

## SHA-256 of reviewed inputs

| Input | SHA-256 |
| --- | --- |
| **`docs/lean/proofs/SP-14/STATEMENT_REVIEW.md`** | **`f507ad236fc7c9e9547ce23ebe74ddffac84872d66648cc8b543ff89d6f39efc`** |
| `eigenvalues-and-inverse-problems/SP-14/README.md` | `9d0c6376080838ea50e8736cb4249276c06a528479fb9c9f565cc7747a485075` |
| `eigenvalues-and-inverse-problems/SP-14/problem.tex` | `286ef6caa3b4e3fce192d8fe133279c98e2d0bdcf3771c6c2969e7c1a58e0957` |
| Source `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Submission `README.md` | `33b422a65e5d9c0b6e81482ff0505d949a7ffcdfed15dd312cd4c75ce259dca2` |
| Source informal `independent-review-2026-10-09.md` | `8fd49126378e6d05e28db4e336fe397ee7dc9dc9a17bbe554fe0f7d6df9a7849` |
| `problem_ids.json` | `d7f9925a483d40030ef266917bc8e413dac6d45530ad5515da506ffe9583e763` |

Any changed source or review bytes require a new fidelity check before implementation.
