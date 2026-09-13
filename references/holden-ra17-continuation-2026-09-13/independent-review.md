# Independent informal review of the RA-17 continuation

**Reviewer:** separate Codex AI agent, independent of the coordinating submission agent.  
**Date:** 13 September 2026.  
**Verdict:** **PASS for the stated partial results; NOT a complete resolution of RA-17.** No Lean verification or external human peer review is claimed.

## Scope and policy

Reviewed `writeup/main.tex`, `writeup/pencil_audit.tex`, and `code/verify_relaxation.py` from `RA17_topological_relaxation_continuation.zip`, comparing the claims with the retained RA-17 README and the repository's resolution policy. The canonical target asks for the exact minimum number of real linear measurements for every admissible dimension and rank. This manuscript deliberately treats the strict range `2r < d`; the boundary `2r = d` is elementary (the difference cone is the whole matrix space, so the count is `d^2`). More substantially, even `mu_R(6,1)` remains between 19 and 20. Thus neither Solved nor Solution claimed is appropriate; retain **Partially resolved** and the original target.

## Mathematical review

- **Section 2, Lemma 2.1 and Propositions 2.2–2.3:** the kernel/difference equivalence is correct. The anti-diagonal Vandermonde construction gives `4r(d-r)` independent integer measurements: a first nonzero anti-diagonal contains at least `2r+1` nonzero entries, and these give a triangular nonzero minor. Odd determinantal degree forces the matching lower bound by generic complex intersection and conjugation parity.
- **Section 3, Theorem 3.1 and Lemma 3.2:** the continuous relaxation proof correctly retains the orientation local system. The projective image-plane resolution is orientable because `k=2r` is even. Its rank-k open stratum is connected, and the explicit path from a matrix to its negative detects the nontrivial sign monodromy. The singular locus has codimension at least three, so the top relative/cohomology comparison and compact-support duality give `H^n(X;Z_lambda)=Z/2`. Reduction to mod two is an isomorphism. The sole obstruction to a section of `n lambda` is therefore detected by degree parity. This proves the asserted critical continuous equivalence, not a linear realization.
- **Section 4, Theorem 4.1 and Corollary 4.2:** the frame criterion uses `N-q=b-1` odd and `q>=2`, so the first Stiefel homotopy group is `Z/2`, with no nontrivial coefficient action. The base dimension leaves only its primary obstruction, `w_b(dQ)`. Generic constant sections identify the obstruction's parity with the determinantal degree: rank-k matrices have a unique c-dimensional nullspace, and lower rank strata are avoided generically. The limiting case `b=2,q=2` is also covered by `V_{3,2}=SO(3)` and its fundamental group `Z/2`.
- **Section 3, Corollary 3.3:** odd polynomial approximation and common-degree homogenization are valid on the compact unit link; the manuscript correctly avoids inferring linear recovery from them.
- **Section 5, Theorem 5.1 and the six-dimensional specialization in Section 5.3:** the even-dimensional rank-one index argument is consistent with the rational Grassmannian ring and its top normalization. The displayed second Stiefel–Whitney classes have integral torsion lifts, justifying Spin-c structures and rational determinant factor one. The residue calculation and half-spin parity refinement produce the stated bound. In dimension six, the rank-six hypothetical complement gives half-index `3/2`, whereas the rank-seven complement gives integral total index 3. The latter is not a construction of a linear kernel.
- **Sections 6.1–6.3:** the rational positive Gram identity and finite-dimensional Hermite trace form are valid sufficient acceptance mechanisms at their stated scope. No new pencil certificate is supplied or accepted by this review. Earlier archives, exploratory searches and all previously reported bounds were not independently re-audited.

The main topological steps show why a bundle-only obstruction cannot close the critical even-degree gap. I found no mathematical correction necessary in those arguments. This is an informal written audit, not a formal proof of every background theorem and not a claim of novelty.

## Reproducible arithmetic

Inspected the script before execution. It writes only its generated JSON data beside the extracted submission. Running `python code/verify_relaxation.py` with Python 3.12.14 and SymPy 1.14.0 returned:

```json
{"status": "PASS", "check_count": 137}
```

The checks cover the rank-two degree identity and binary valuation for dimensions 3–64, twelve formal-series coefficients, degree parity samples, exact measurement ranks/kernel dimensions for five exported systems, a mod-two Grassmannian reduction, and the dimension-six index values. These are arithmetic checks, not a substitute for the topological review. Both system and bundled default Python initially lacked SymPy; the successful run used the existing `/private/tmp/ra05-env/bin/python` environment.

An additional independent symbolic calculation, separate from the submitted checker, expanded
`((z/2)/sinh(z/2))^6 sinh(z)/z` and `4/cosh(z/2)^6` through degree four. It obtained respectively `1-z^2/12` and `4-3z^2+5z^4/4`; their product has degree-four coefficient `3/2`, confirming the displayed six-dimensional half-index.

## Source checks and presentation

The Stiefel homotopy calculation and primary obstruction identification were checked against [Hatcher, Vector Bundles and K-Theory, Section 3.3, Lemma 3.20 and Proposition 3.21](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf). These support precisely the obstruction step used above. The [Carlson arXiv record](https://arxiv.org/abs/1611.01175) identifies the cited work as *Grassmannians and the equivariant cohomology of isotropy actions*, version 2 dated 27 November 2023; the bibliography should use this title rather than only its arXiv identifier. The generic statement that the archive has not been independently reviewed should be updated in the submitted edition to distinguish this informal audit from external human peer review.

**Recommended disposition:** accept as an attributed, independently informally reviewed continuation with exact critical topological relaxations, preserve RA-17 as Partially resolved, and do not claim that the unresolved linear classification or any new critical pencil has been solved.
