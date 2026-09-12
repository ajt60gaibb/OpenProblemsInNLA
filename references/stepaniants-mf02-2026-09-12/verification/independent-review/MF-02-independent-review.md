# MF-02 independent mathematical and scope review

Reviewer: separate Codex agent `/root/prepare_manuscripts`  
Review date: 12 September 2026 (UTC)

**Mathematical verdict: PASS for the stated theorem.** I independently reconstructed all the proof steps and found no mathematical gap. No numerical experiment or assumed attainment of an infimum is needed.

**Canonical scope verdict: PASS for uniform asymptotic order.** The theorem proves that the quantity in the retained canonical MF-02 statement is `Theta(m+1)`, with absolute constants uniform for every `0 < delta < 1`. Under the standard constant-factor meaning of asymptotic order, this determines the canonical dependence on both parameters.

**Original-source exact-optimization verdict: PARTIAL.** The proof does not identify the exact smallest number of stages, a sharp asymptotic constant, or the comparison of the two errors at the same multiplication budget. It must not be described as a complete exact solution of workshop Problem 6.5. A status notice referring to the canonical asymptotic-order result should explicitly retain this distinction. If a status instead purports to cover the entire stronger original optimization question, “partially resolved” is the appropriate description.

This report makes no novelty, public-priority, or publication-eligibility determination. In particular it does not claim that uniform constant-factor order was previously unknown. The separate source audit must be considered before any attribution or submission decision.

## Exact inputs and independence

I read the canonical target and the primary workshop question before reading the candidate. I did not write the candidate or use an author's algebra checker. I independently wrote [exact_algebra_check.py](exact_algebra_check.py). The candidate and repository were not edited during this review.

| Input | Bytes | SHA-256 |
| --- | ---: | --- |
| [Reviewed candidate snapshot](reviewed-candidate.md), originally `../RESULT.md` | 11,177 | `63d6a0dccebaf43b7da3dc6b2615755c3c3d24791a12527007f1276256e89ba9` |
| [Canonical target snapshot](canonical-target.md), from `matrix-functions-and-stability/MF-02/README.md` | 2,393 | `1312362ce7bbe162adba3b9305acd2f8cd31dd7d8c8d056ce0138c0b25243127` |
| [Independent exact checker](exact_algebra_check.py) | See manifest | `f0fd801ff50999a61633e84619657720dee2e1dddeec24d7f2791f92012ec673` |

The canonical snapshot in this table is the page read from `/tmp/nla-sp15-worktree`. Exact file fingerprints, including this report and the checker output, are also recorded in [manifest.json](manifest.json).

## Target and source comparison

The canonical target uses real straight-line polynomials starting from `1,x`, free real linear combinations, at most `m` nonscalar products, arbitrary stored-value reuse, and a single polynomial identity valid in every matrix size. It uses infima for both approximation classes, allows every nonnegative integer stage count, and fixes the empty composition to `x`. These definitions are retained by the candidate.

The primary [Amsel et al. workshop report, version 3, Section 6.3, Problem 6.5](https://arxiv.org/html/2602.05394v3#S6.SS3) asks about same-budget approximation errors and alternatively the smallest admissible stage count. Its equations (21)–(22) use minima; the canonical infimum formulation avoids assuming those minima exist. The candidate correctly proves statements for infima. The primary question is therefore broader in requested precision than a uniform constant-factor answer.

The canonical asymptotic claim is meaningful even for a sequence of gaps approaching either endpoint: the two constants are independent of the gap, so no unbounded additional gap-dependent factor remains. The bounds leave a bounded factor, possible gap dependence within that factor, and exact integer values undetermined. This is why the two scope verdicts above are different.

## Independent proof audit

### 1. Degree-only lower bound

Write `r=(1-delta)/(1+delta)`, which is strictly between zero and one. The proof of the real Chebyshev comparison is valid for every integer degree bound `D >= 1`. At the `D+1` alternating extrema, a supposed violating comparison produces `D` distinct interior roots, plus the external root. Strict alternation also excludes the identically zero polynomial. Reflection handles negative external arguments.

For an approximation error `0 < e < 1`, odd symmetrization cannot increase the uniform error on the symmetric domain. This operation is used only to establish a degree bound, not to assert preservation of the multiplication budget. Squaring the odd polynomial gives `B(x^2)` with `B(0)=0` and degree at most `D`. Its range on the positive interval gives the bound for the auxiliary polynomial `H`. The affine interval transformation, the positive Chebyshev value, and the hyperbolic formula then yield

\[
\frac{e+e^{-1}}2\le\frac{r^D+r^{-D}}2.
\]

The scalar function on the left is strictly decreasing for `0 < e < 1`; hence `e >= r^D`, with the required inequality direction. Errors at least one cause no difficulty. Error zero is impossible because the two nondegenerate intervals demand incompatible polynomial identities.

The largest available degree starts at one, free linear combinations preserve its bound, and a product at most doubles it. This remains valid with reuse and arbitrarily many free linear combinations. Thus `E_m >= r^(2^m)`. Cubic compositions similarly satisfy `C_T >= r^(3^T) > 0`. These are pointwise bounds uniform over their coefficient sets, so they pass to the infima without compactness or attainment assumptions.

### 2. Cubic interval construction

With `A=1+a+a^2`, the point `sqrt(A/3)` lies strictly inside `(a,1)` for every `0 < a < 1`. Direct differentiation gives a unique interior maximum of `x(A-x^2)`, and its two endpoint values agree at `a(1+a)`. Consequently the normalized odd cubic has exactly the asserted positive image interval, with `0 < phi(a) < 1`.

I independently expanded the polynomial comparison in equation (10). After the positive factors are canceled and both positive sides are squared, the residual is

\[
(1-a)^2(11a^4+28a^3+30a^2+28a+11)>0.
\]

This proves the stated weak inequality and in fact strictness on the open interval. Applying the decreasing positive-argument Möbius map gives the error-ratio squaring inequality with the stated direction. No limit regime or numerical estimate is involved.

The recursively generated gaps all remain strictly between zero and one. Induction therefore justifies every stage of the image-interval construction. Oddness transfers the same error estimate to the negative interval. Multiplication of the final output by a scalar is absorbed into the last cubic's two coefficients when `T >= 1`, so it does not add a stage. This yields `C_T <= r^(2^T)` for every positive integer `T`.

All the coefficients used here are allowed real coefficients depending on the fixed gap and stage count. Their generation is not a charged matrix product in the stated model. Each cubic is evaluated by forming the square and then the cube, with at most two nonscalar products. No extra division or matrix-dependent primitive is introduced.

### 3. Strict decrease and infima

The empty composition has error `1-delta`. The constructed one-stage error satisfies `r^2 < 1-delta`, so the initial strict step is valid.

For every subsequent fixed stage count, the preceding upper and lower bounds imply `0 < C_T < 1`. An actual composition with error `e < 1` maps the positive interval into `[1-e,1+e]`. Dividing the scalar argument by `1+e` and applying one additional allowed cubic yields error at most `e^2`; both scalar factors belong to that new stage's coefficients.

A minimizing sequence of actual stage compositions has errors eventually below one. Applying the construction to each member and taking the limit gives `C_(T+1) <= C_T^2 < C_T`. Neither a minimizer nor a coefficient-convergent subsequence is needed. Strict positivity, already proved separately, is essential and is available at every finite stage.

### 4. Stage bounds, small cases, and quantifiers

Combining the degree lower bound with the constructed `m`-stage upper bound proves admissibility at `T=m` for `m >= 1`. For `k=floor(m/2) >= 1`, every `k`-stage composition belongs to the unrestricted class with at most `m` products, so `E_m <= C_k`. Strict decrease excludes every stage count below `k`. The direction of both comparisons is correct.

With zero products the unrestricted class is affine. With one product its degree is at most two, whose odd part is linear. The linear minimax bound together with `2x/(1+delta)` therefore gives `E_0=E_1=r`. The empty composition fails this error target, and a single cubic meets it, proving both exact small values.

For `m >= 2`, the elementary parity check gives `floor(m/2) >= (m+1)/4`; the two smaller cases satisfy the same global inequality. The admissible set is nonempty, so its infimum over nonnegative integers is a finite attained integer minimum. This last discrete attainment is distinct from, and does not assume, attainment of the polynomial-error infima.

All statements hold for each `0 < delta < 1`; neither endpoint is silently included. No estimate presumes a gap bounded away from zero or one. Stored-value reuse, degenerate cubic coefficients, constant or lower-degree polynomials, and arbitrary real free linear combinations are covered. The matrix identity holds in every size because the evaluator is a scalar-coefficient polynomial program.

The theorem gives an upper guarantee of at most `2m` products, not a proof of the optimal product overhead, the necessity of two products for every chosen stage, or an optimal leading stage constant.

## Exact reproducibility evidence

Run from this directory:

```bash
python3 exact_algebra_check.py --output exact-algebra-output.json
```

The independent checker passes **17 exact checks** using only Python's standard-library rational arithmetic: 15 polynomial identities and two coefficient-sign checks. These include the main sixth-degree factorization, strict interior-maximum factorization, the Möbius identities, the positive-denominator hyperbolic identity, endpoint rescaling, and the final parity inequalities. They are polynomial coefficient comparisons, not tests at sample points. The [output](exact-algebra-output.json) binds both reviewed inputs and the checker by SHA-256.

The all-degree Chebyshev argument, infinite parameter ranges, circuit-degree argument, infimum reasoning, and scope judgment are justified in the written proof and audit. The finite algebra checker does not replace those arguments.

## Required correction and review limits

One bibliographic correction is required before submission: Section 6's `H. Lorentzon` should be **G. Lorentzon**. The [primary version-1 author block](https://arxiv.org/html/2606.24701v1) names Gustaf Lorentzon. This correction is outside the mathematical proof and does not affect the verdict. I have not modified the frozen input; its recorded hash includes the typo.

No mathematical correction is required by this review. The frozen candidate itself expressly acknowledges the exact-minimum limitation. Any later editorial expansion to an unqualified exact resolution would go beyond this PASS.

This is an independent Codex-agent mathematical audit, not external human peer review, proof-assistant verification, or a formal certificate. It does not certify originality, priority, absence of a competing public solution, or final typesetting. The separate literature and current-public-status audits remain necessary for a publication decision. No repository status was changed as part of this review.

Signed: **Codex agent `/root/prepare_manuscripts`**, 12 September 2026 (UTC).
