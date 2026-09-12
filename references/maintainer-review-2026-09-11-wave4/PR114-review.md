# Independent audit of PR #114

Reviewed head: `1edaf118df2258c1b20c75966807219075d2ddf7`.
Verdict: PASS mathematical review; no blocker found. Integration/CI left to root.

Read the complete authored tr17_solution.tex and tr27_solution.tex against origin/main's canonical TR-17 and TR-27 pages. Both preserve and resolve the exact original mathematical targets; no ID/path reassignment found in the reviewed canonical updates.

TR-17: checked positivity/coercivity on every real affine product chart; dominance and generic finiteness of the block-gradient map; logarithmic resolution with nonzero residues on every boundary component (including nonreduced and singular divisors); zero-scheme/top-Chern count; product-linear CSM-section inversion; nonnegative coefficient identity; and the Frobenius equality case. Aluffi–Harris Theorem 8.1 and equations (7.3)/(7.4) give exactly the external ED/CSM facts used, without assuming smooth quadric intersection. The general-form and all-section arguments cover the original positive-definite complex-bilinear convention.

TR-27: checked rational-normal-curve tangent rank D via the polynomial annihilator, projection-center rank at least D-r, preservation of independence of all sets of at most r^m-1 distinct points, uniqueness proof of rank r, tangent border rank 2, and product-basis support lower bound r^k. The Hankel factorization proves the center avoids secant/tangent loci, yielding smoothness. The explicit curve is reduced, irreducible, nondegenerate and fits the original general-variety target; no extra Segre/Veronese restriction is silently assumed.

Checks: submitted TR-17 standard-library exact verifier passed 1674 coefficient cases, 1776 formats and 178 smooth-divisor checks. New independent standard-library rational checker `/private/tmp/nla-review-tensors/independent_checks.py` reconstructed the TR-27 quotient/kernel and rank-12 minor, three-term and nine-term decompositions and Hankel determinant 5184; all passed. The submitted TR-27 SymPy verifier could not run because SymPy is unavailable in both system and bundled Python; its decisive certificates were independently reproduced.

Sources inspected:
- https://arxiv.org/pdf/1708.00024 (Aluffi–Harris, Thm 8.1, (7.3), (7.4)).
- https://arxiv.org/html/2309.15105v3 (Conjecture 3.9).
- https://arxiv.org/html/1909.03811v2 (Conjecture 1.1 and eventual-power scope).

PDF visual QA: rendered and visually inspected all 17 pages of the two authored manuscripts (7+6 pages) and two canonical problem PDFs (2+2 pages). Equations, symbols, hyperlinks, paragraph boundaries and page layouts are readable without substantive clipping or overlap. PDF text bounding boxes confirm both canonical headers and footers remain inside A4 page bounds. No PDF blocker found.
