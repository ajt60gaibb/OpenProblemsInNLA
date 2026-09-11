# MI-21 independent proof review

**Verdict: PASS — complete negative resolution of the exact canonical universal target.**

Review date: 11 September 2026. Reviewer: independent agent `/root/review_matrix_exact`. Read the entire original `.cache/colbrook-matrix-submission/nla_submission/proofs/MI-21.tex`, `preamble.tex`, relevant bibliography, and `matrix-inequalities-and-norms/MI-21/README.md`. No original proof or canonical file was edited.

## Full original identity

Full-file SHA-256 after UTF-8 decoding and LF normalization, with no trimming: `e3ec2bf542cc2adc0249ac90a9d01c557615cde0938cdd68e85c6ce5d60236e1`. Original and normalized lengths: 3,142 bytes; no bare CR. The entire section, theorem, proof, and remark are covered. PASS attaches to this original identity and the canonical target read today.

## Exact target match

The target quantifies over positive definite inputs, every unitarily invariant norm, t in [0,1], p,r,s > 0 with sr >= 1, and all positive dimensions and summand counts. Here m = n = 2, s = t = 1/2, r = 2, so sr = 1. The operator norm is unitarily invariant. A failure for this norm suffices. Since both aggregate matrices equal I, the same example applies to every p > 0 without any fractional-power numerical calculation.

The publisher's Conjecture 3 has precisely these power placements and parameter conditions; in particular it does not impose s >= 1 or rp >= 1 on this conjecture. Independently checked [Freewan–Hayajneh, printed p. 195, Conjecture 3](https://files.ele-math.com/articles/mia-27-15.pdf). Conditions from preceding proved statements must not be imported into it.

## Admissibility and mean identities

Both diagonal C,E have strictly positive entries. Direct arithmetic gives C^2 + E^2 = I: the numerators are the Pythagorean pairs (12,35,37) and (21,20,29). The displayed symmetric S has S^2 = I because 15^2 + 8^2 = 17^2 and its off-diagonal cross terms cancel. Hence conjugating either positive diagonal square by S preserves PD. All four A_i,B_i are rational PD and each aggregate is I.

Spectral square roots give A_1^(1/2) = C, A_2^(1/2) = E, B_1^(1/2) = SES, B_2^(1/2) = SCS. By symmetry and unitary covariance of the ordinary positive geometric mean, S(C#SES)S = (SCS)#E = E#(SCS). Squaring gives exactly the two terms G^2 and SG^2S. There is no illicit commutation or replacement of a geometric mean by an entrywise operation.

For arbitrary 2 by 2 PD C,D, put Y = C^(-1/2) D C^(-1/2) and delta = sqrt(det Y). Cayley–Hamilton gives (Y + delta I)^2 = (tr Y + 2 delta)Y. The proposed square root is positive because Y + delta I is PD and its scalar denominator is positive. Congruence by C^(1/2) yields G = (D + delta C)/sqrt(h). Thus the manuscript's square-root formula is justified, not merely an algebraic root with unspecified sign.

## Exact certificates

A separate standard-library Fraction calculation regenerated every displayed rational matrix, without importing or reading the supplied verifier. It confirms:

- delta = 5/3 and h = 61697295/8682716;
- D + delta C = [[443355,33000],[33000,605715]]/310097;
- G^2 = [[3516940,616000],[616000,6547660]]/12158163;
- L = [[8216600,-985600],[-985600,11912600]]/12158163.

Direct exact multiplication gives L(1,-4)^T = (1351000/1350907)(1,-4)^T. Its eigenvalue exceeds one by 93/1350907. The other eigenvalue, checked both by trace and the characteristic determinant, is 7970200/12158163, strictly between zero and one. L is positive as a sum of positive squares; consequently its operator norm is its largest eigenvalue, and is greater than the norm of I. No rounding can change the sign of this rational gap.

## Limits

No material gap was found. The universal weighted conjecture is refuted by a valid boundary point sr = 1; this does not assert failure in all other parameter regimes or in all unitarily invariant norms. The assertion that the same inputs work for all p > 0 is fully justified by A = B = I. Literature priority and an exhaustive resolution search were not reviewed. This is an independent agent audit, not external human peer review or machine-checked formal proof. Reproducible supplemental arithmetic is retained in `independent_exact_counterexamples.py`.
