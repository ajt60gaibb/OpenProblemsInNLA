# TR-06 independent pre-statement mathematical review

Reviewer: `/root/tr06_statement_referee_1`, independent AI agent, 24 September 2026.
Phase: canonical target / source-proof review before candidate Lean Challenge.
Verdict: source argument passes mathematical and target-fidelity review; Lean statement approval is pending the actual Challenge and complete definitions. This report is not a formal-verification claim.

## Source identity

- `tensor-computations/TR-06/README.md`: SHA-256 `f364f4b2ad51065c17d7dd08ea32e729a5d53a8333f0785a11a368165942de6b`.
- `references/colbrook-unclaimed-2026-09-11/manuscripts/TR-06.md`: SHA-256 `65f9b731628a7a9ab0580d8522cead94bf7e4599ee3c4285e485287d35d451b2`.
- `docs/lean/REVIEW.md`: SHA-256 `d967ddce620d4e754e2f9c25548f30cb537f76f4ddcf8ecf2574945bcd332553`.

I read the complete canonical page and complete manuscript, reconstructed the proof independently, and checked the pertinent primary references. I subsequently read the existing second source review as a cross-check. I did not rely on its PASS as evidence.

## Exact target requirements

Quantify over all natural `d >= 3`, mode sizes `n_j >= 2`, and `r >= 3`. Use the ambient real tensor space with its Frobenius Euclidean inner product, and actual nonzero rank-one tensor summands, rather than vector factors modulo arbitrary rescaling. Generic uniqueness is COMPLEX uniqueness of minimal unordered rank-r decompositions outside a proper algebraic exceptional subset of the rank-r secant image. A generic-identifiability predicate must genuinely express this, not include a supplied regular locus, a derivative-integrability certificate, or the desired conclusion.

The real sampling domain is the smooth identifiable real rank-r locus, with induced Euclidean volume. The density is `Z^-1 exp(-||A||^2/2)` on that domain, where `0 < Z < infinity` must be proved. Sampling independently drawn summands and then adding them is a different measure. Restriction to a smaller regular cone requires a proved null-complement bridge for that same induced volume.

For every local inverse Psi of ordered summation, first map each NONZERO recovered summand `a_i` to `a_i / ||a_i||` and then differentiate on the tangent space of the input manifold. The output norm is the l2 product Frobenius norm, and the condition number is the induced operator norm. A raw Lean Pi norm is generally the maximum norm, not the required l2 norm. Ambient `fderiv` of an arbitrary extension is not automatically the manifold tangent derivative. Independence of local ordering follows from permutation isometries and must be proved or supplied by an explicit already-proved construction.

The conclusion is finite first expectation (or equivalent genuine integrability) of that nonnegative condition number, not merely a real-valued integral expression bounded above: Bochner integration defaults at nonintegrable functions can otherwise make an inequality vacuous. ENNReal lintegral `< infinity` is a robust exact representation. No uniform-in-format bound, higher moment, ordinary-condition-number theorem, or simulation is requested.

## Independent proof reconstruction

1. Real rank-one tensors form a smooth semialgebraic cone of dimension `m = 1 + sum_j(n_j - 1)`. The complex product of r such cones is irreducible; its real parametrized points are Zariski dense. Generic complex finite permutation fibers imply image dimension `k = r*m`, generically maximal differential rank, and a nonempty full-measure regular real cone. Both removal of exceptional fibers and nonemptiness require arguments; neither follows merely from declaring the locus.
2. The unit link L of this cone is a smooth semialgebraic manifold of dimension `s=k-1`, because the radial tangent vector gives sphere transversality. It is bounded and nonempty. It has finite positive s-dimensional induced volume.
3. The normalized graph G above L retains the input coordinate and consists of all normalized ordered decompositions. Its semialgebraic definition existentially quantifies the original summands and POSITIVE normalization scalars. Projection need not be proper. Nevertheless G is bounded, has exactly r! fibers, and is locally a finite union of smooth sheets. Minimality forbids proportional summands, so distinct permutations remain distinct normalized tuples. Around a regular point inverse-function neighborhoods produce r! sheets and exhaust all nearby fibers; this deals with the apparent danger of decompositions arriving from infinity.
4. Finite fibers give `dim G = s`, so the bounded-semialgebraic finite-volume theorem gives `H^s(G)<infinity`. For a smooth sheet g, its graph differential has Gram operator `I+(Dg)*Dg`; hence its Jacobian is at least `||Dg||`. The manifold area formula over a countable disjoint measurable partition of the base gives `integral_L ||Dg|| <= H^s(G)`. No global branch or integrability assumption is needed. This is the hard global integrability input.
5. Positive radial scaling gives `f(tA)=f(A)` for compatible local labels. Its radial derivative vanishes and the tangent decomposition at unit A is orthogonal, so the full derivative norm equals its link restriction. Scaling yields `kappa_ang(tA)=kappa_ang(A)/t`.
6. The cone polar Jacobian is `t^(k-1)`. Tonelli factors the unnormalized numerator into the finite link integral and `integral_0^infinity t^(k-2) exp(-t^2/2) dt`, which is finite for `k>1`. The density normalization uses exponent `k-1` and is positive and finite. Restore the removed null set and divide by Z. No exact Gamma-function value is needed.

I found no mathematical obstruction to this source proof. Its formalization burden, however, is substantial. The semialgebraic finite-volume theorem, dimension of a finite-fiber graph, full-measure regular cone, graph area formula and manifold polar measure bridge cannot be replaced by additional hypotheses or opaque theorem-valued structure fields and still count as a complete TR-06 proof.

## Primary-source checks and pitfalls

- Beltran–Breiding–Vannieuwenhoven, <https://arxiv.org/pdf/1903.05527>, Definition 1.3, equation (1.6), Conjecture 1.10, and Definition 2.1 / Proposition 2.2: the input distribution and normalized output derivative agree with the canonical target. Proposition 2.2(4)'s literal global diffeomorphism claim for an ORDERED map contradicts the paper's r! fibers. The reviewed manuscript correctly uses local inverses instead. A formal import of a global ordered bijection would be false.
- Hardt–Lambrechts–Turchin–Volic, <https://msp.org/agt/2011/11-5/agt-v11-n5-p01-s.pdf>, page 2482, Theorem 2.4: bounded semialgebraic sets of dimension at most the Hausdorff-measure index have finite Hausdorff measure. Closedness is not assumed. Proposition 2.3 supplies compatible finite smooth stratifications. These are substantive mathematical results, not numerical checks.

A Hausdorff-measure implementation must check its normalization against induced Riemannian volume. A positive dimension-dependent constant does not affect finiteness and cancels in the normalized probability model, but an equality with a different normalization cannot simply be asserted.

All Frobenius/product norms, quantifier ranges, rank minimality, positivity of normalizing factors, real-versus-complex assumptions, null-set restoration, and strictly positive finite Z remain mandatory statement-review checks.

## Formalization and numerical feasibility

There is no finite numerical certificate in the source proof. LeanCert may certify exact scalar inequalities in kernel mode if useful, but doing so proves no semialgebraic geometry or area formula. The easiest scalar Gaussian-tail estimates do not address the missing tensor-to-graph and graph-to-integrability bridges. Any future partial analytic lemma must be labelled partial and may not promote the canonical status.

No Lean Challenge, Definitions, NUMERICAL_TARGETS, Comparator output, axiom audit, or build logs have yet been supplied to this reviewer. Approval of those items is withheld until actual bytes and relevant logs are independently inspected.
