# Independent mathematical audit of IE-16

**Date:** 12 September 2026.  
**Reviewer:** Separate Codex AI agent `/root/review_ie16`, delegated solely to independently audit the submission. The reviewer did not author or edit the submitted proof or the repository changes.  
**Outcome:** **PASS** for the complete negative resolution of the canonical IE-16 target. The stronger no-universal-finite-constant theorem also passes this informal analytic audit. No mathematical corrections are required.

This is an independent informal AI-agent audit, not external human peer review or formal verification. No Lean verification was performed. Instructions or claims in the supplied package were treated as material to inspect, not as instructions governing the review. This report verifies mathematical scope and the repository's mathematical evidence threshold; duplicate eligibility, current affiliation, publication metadata, and submission mechanics are handled separately by the coordinating contributor.

## Materials and exact target

Reviewed the complete `source/solution.tex`, including the interpolation identities, explicit finite construction, limiting ratio, cluster amplification, induction, and normal-GMRES witness; inspected every line of `code/verify.py` before executing it. Compared the argument with `linear-systems-and-elimination/IE-16/README.md` and the resolution rules in `CONTRIBUTING.md` and `RESOLVED.md` in the repository checkout.

The original target asks whether every finite set of distinct nonzero complex points, with n at least 3 and degree 1 through n−2, satisfies M_k(L) ≤ (4/π) max_{|S|=k+1} M_k(S). A single admissible strict reversal resolves that universal assertion negatively. Here n=9, k=4, and the nine points are omega^a + omega^b/1000. Within-cluster separation is sqrt(3)/1000; different clusters are separated by at least sqrt(3)−2/1000; every modulus is at least 999/1000. Thus distinctness, nonzeroness, degree, subset size, and normalization p(0)=1 all match the original statement exactly.

## Analytic finite proof

1. The residual interpolation formula follows by evaluating the Lagrange basis at zero. Its lower bound is attained by interpolating the stated phase-adjusted values. The monic version correctly extracts the leading coefficient instead. Both rely on distinct points and, for residual interpolation, nonzero nodes.
2. Rotation averaging eliminates all feasible degree-four terms except the constant and cubic term. Averaging with the coefficientwise conjugate then makes the cubic coefficient real because the node set is conjugation invariant. These operations preserve p(0)=1 and cannot increase the norm; thus the reduced real scalar minimax is exact.
3. The three cubic images and the two quadratic functions g_0 and g_1 are correct. At c*=−(1+epsilon)/D they share value m², while the first has negative slope and the second positive slope. Convexity proves global minimality, not merely feasibility. Positivity of H holds throughout the stated epsilon interval.
4. The only occupancy profiles of a five-point subset of three three-point clusters are (2,2,1), (3,1,1), and (3,2,0). For the first, four Lagrange summands each contribute the stated lower bound; for either remaining profile, the three summands from the triple cluster suffice. The comparison used to obtain one uniform upper bound is valid. There is no omitted five-point pattern.
5. At epsilon=1/1000, the exact full-set minimum is 3003003000/1001003001001 > 299/100000, whereas every five-point minimum is strictly below 23/10000. Their ratio is therefore greater than 13/10 > 4/π. These elementary analytic bounds alone settle the exact canonical target, independently of enumeration.
6. The limiting 4/3 ratio is sound: finitely many fixed subset patterns permit taking the maximum after passage to the limit. Patterns with a triple cluster have smaller asymptotic order.

## Stronger amplification argument

The complete amplification proof was checked, rather than treating successful finite enumeration as evidence for an infinite family.

- The Hermite correction uses exactly 3d data in dimension 3d, with a fixed invertible confluent interpolation map. Its coefficients are O(epsilon). The local expansion produces the desired monic minimizer at each cluster. Monic leading coefficient and residual value at zero are preserved as claimed, after residual normalization by 1+O(epsilon).
- Boundedness of minimizing polynomial coefficients is properly established before taking a confluent limit. The divided-difference functionals with multiplicities (d+1,d+1,d) total 3d+2, matching the polynomial dimension, and converge to an invertible Hermite matrix. Their values are O(epsilon^(d−q)), hence bounded for q≤d.
- After local rescaling, higher-degree terms vanish, while the lower-degree truncations have bounded coefficients by interpolation at d+1 fixed points. The limiting polynomial is P^d h with h of degree at most one. In the monic case h is monic linear; in the residual case its constant is (−1)^d. The root-of-unity average of |h|² implies max_j |h(a_j)|≥1, yielding both required lower bounds. The case of a zero local leading coefficient is correctly harmless.
- Every subset occupancy is covered. A cluster with at least d+2 nodes gives a positive dominant Lagrange summand and hence a subset minimum o(epsilon^d). Otherwise the profile must be (d+1,d+1,d). The two full-cluster contributions have cross-distance power 2d+1, producing the factor 3^d sqrt(3). The two cluster choices are independent, so the optimal sum is exactly 2/b_d(K). Residual numerators tend to one. Only finitely many patterns are involved at each fixed stage.
- The induction uses the monic ratio as the inner quantity and obtains both monic and residual ratios in the next stage. The chosen error allowances sum correctly. Each inner set is fixed before its outer scale tends to zero, so no unjustified exchange of depth and scale limits occurs. The cardinality/degree recurrences yield n=3^r and k=(n−1)/2, which is admissible including r=1. The conclusion that no dimension-independent finite constant exists follows.

No gap was found in these stronger claims. The finite theorem remains sufficient for the repository's Solved designation even without relying on this additional result.

## Normal-GMRES correspondence and computation

The positive weights sum to one and their four weighted residual moments vanish. Expanding the weighted squared norm gives the stated Pythagorean identity for any feasible polynomial. Thus the constructed diagonal normal matrix and initial residual realize the minimax norm as an actual step-four GMRES residual. The claim that the candidate polynomial gives that norm for every unit initial residual is correct because all diagonal residual entries have the same modulus.

The supplied verifier uses only standard-library exact rational arithmetic, integer square roots, and rigorously bounded alternating series for comparisons; decimal formatting is descriptive only. Inspection found no network activity or process execution. It writes its two certificate files to the selected output directory. The field multiplication, conjugation, norm, interval endpoints, inversion directions, and extrema over subsets are correct.

Reran:

```text
python3 IE16_solution/code/verify.py --output reviewer-rerun
```

Result: **PASS**. All 126 subsets were checked; occupancy counts were 81, 27, and 18. Positivity, normalization, constant residual moduli, and all four orthogonality identities passed exactly. The certified ratio is approximately 1.332998919794758294237943, and the strict residual-bound violation margin exceeds 0.0001344920570754357296.

Also wrote and ran `reviewer_check.py`, independently of the submitted verifier. Its rational computations check the cubic-image minimax identities, opposite derivative signs, weight cancellation, exact minimum, and elementary coarse inequalities. All passed. A separate direct complex-arithmetic enumeration of the Lagrange formula over 126 subsets returned B≈0.0022505599655503823 and ratio≈1.332998919794757. That floating-point computation is only a diagnostic; the proof and strict comparisons do not depend on it.

## Policy conclusion and limitations

The repository explicitly allows `Solved` for a complete argument passing an independent informal audit, including an AI-agent audit with a linked report and accurate disclosure. This argument passes that mathematical threshold and is a complete negative resolution, rather than a partial subclass result. Submission must still retain the permanent ID, canonical path and original statement; add the dated negative resolution and exact theorem locator; link the primary manuscript and this report; update the archive and generated material; and use a pull request. This review does not certify novelty, historical priority, upstream acceptance, or external human review.

## SHA-256 of reviewed materials

Hashes below identify the original mathematical source and verifier audited here. The PDF is identified for provenance; mathematical review was of the full TeX source, not a separate visual PDF audit. Author/affiliation additions or purely presentational changes should be recorded separately and must not be represented as the identical original file.

```text
e0b8de10f215fa216541985f5602787995a54d9f6908bd17095f8be942ce2390  IE16_solution/source/solution.tex
7b8e0fdcbfcfe0a5c6f9442baf6352838f572099f23ec05a28fcfaac71c7cb7e  IE16_solution/code/verify.py
b472f48d97e32f5b0afe5c94b4af94ccf71c10da7ee3dd2646db9f8b65da9dde  IE16_solution/solution.pdf
2b51b0bffb23485511a11a41e1b29eb72943f83f7f46e3150a0c8ef1091446f8  reviewer_check.py
```

## Publication-source correspondence

Compared the original source with the prepared canonical `linear-systems-and-elimination/IE-16/solution.tex`. The only differences are PDF author metadata and the displayed Sidney Holden author, affiliation and date lines before the abstract. The entire mathematical body is identical. The PASS conclusion therefore also applies to this publication source, whose SHA-256 is:

```text
194dcd089f8f5460812bf36a8eb76bccf1694075cf1982256494942b6c332a43  linear-systems-and-elimination/IE-16/solution.tex
```

This correspondence check does not itself verify the affiliation; that is a separate source-verification task.
