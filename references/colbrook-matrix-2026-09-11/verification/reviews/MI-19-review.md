# MI-19 independent proof review

**Verdict: PASS — complete negative resolution of the exact canonical universal target.**

Review date: 11 September 2026. Reviewer: independent agent `/root/review_matrix_exact`. The entire original `.cache/colbrook-matrix-submission/nla_submission/proofs/MI-19.tex` was read, together with `preamble.tex`, the relevant bibliography, and `matrix-inequalities-and-norms/MI-19/README.md`. No proof or canonical file was edited.

## Full original identity

SHA-256 of the entire original TeX decoded as UTF-8, normalized to LF, and re-encoded as UTF-8 without trimming: `c2d54f8abe9fac7a935e990827f6b471390f1c9708c0267f5d631f8879dac3f1`. Original and normalized lengths: 2,270 bytes. No bare CR was present. The identity includes the entire section and remark, not an extracted proof environment. PASS applies to this exact original and the canonical target read on the review date.

## Target, source, and quantifiers

The canonical target concerns every Hermitian PSD matrix of order at least two, q in [0,1], and nonempty proper subset S, with inversions counted in the full index ordering on both sides. The proof adopts exactly that convention. A real symmetric order-four PSD example, q = 7/8 and S = {2}, is admissible. Neither entrywise nonnegativity nor positive definiteness is a target hypothesis. The source's subset-preserving conjecture and its initial-segment theorem are distinct; the example uses an interior singleton. Independently checked [da Fonseca, §5, Conjecture 3 and Theorem 5.1](https://arxiv.org/pdf/1804.02231). The PDF text extraction renders some weak inequality glyphs poorly; the strict negative certificate refutes even the canonical weak comparison, so that extraction ambiguity has no effect.

## Construction and every exact calculation

Multiplying the displayed X transpose by X reproduces all sixteen entries of A. The two rows of X are independent (the second column separates them), so rank(X) = rank(A) = 2. Thus A is PSD with no numerical eigenvalue assumption.

I wrote a separate standard-library Fraction calculation without reading or importing the submitted verifier. Enumerating all 24 permutations, counting every pair i < j with sigma(i) > sigma(j), and multiplying the four indicated entries gives the following coefficients in ascending powers q^0 through q^6:

| Sum | Coefficients |
|---|---|
| Full q-permanent | 4999700, 4886140, -199231, 4712758, 9568969, 4886140, 115600 |
| Restricted sum | 4999700, 4741130, 0, 4741130, 9482260, 4999700, 0 |

The restriction is sigma(2) = 2 in one-based indexing, exactly equivalent to setwise preservation of S = {2}. It selects 3! = 6 permutations. In particular, its exponent is never recomputed after deleting the second index. Both complete polynomials match the manuscript.

Subtracting these coefficient lists and independently expanding q(q+1) times the quartic with ascending coefficients 145010, -344241, 315869, -229160, 115600 gives identical results. Exact substitution q = 7/8 yields

\[
P_q(A)-R_{q,S}(A)=-3235575/16384<0.
\]

This is a strict reversed comparison in the required domain, which is enough to refute a universal statement.

## Positive definite extension and limits

The auxiliary PD assertion is valid: A + epsilon I is PD for every epsilon > 0, and for fixed q,S the difference is a polynomial in the matrix entries. Its value is strictly negative at epsilon = 0, so it remains negative for every sufficiently small positive epsilon. No explicit epsilon threshold is needed for this existence claim. This reasoning does not assert that arbitrary epsilon works.

No material mathematical gap was found. This audit verifies the stated counterexample and its PD persistence; it does not address MI-18 monotonicity, classify surviving subsets, establish minimal order independently of the cited literature, or certify novelty. Primary-source checking was bounded, not an exhaustive priority search. This is independent agent review, not human peer review or formal proof verification. The retained `independent_exact_counterexamples.py` provides reproducible supplemental exact arithmetic; the mathematical argument above supplies the hypothesis and quantifier checks that computation alone cannot supply.
