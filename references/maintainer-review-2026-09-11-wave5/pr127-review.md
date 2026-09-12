# Independent audit: PR127, IE-05

Reviewed head: `e5ad08c1a301d532ea200df8580224bb893b2240` in `/private/tmp/nla-pr127`.

Verdict: **PASS — complete negative resolution of the existing universal extremizer equality. No mathematical blockers found.** This review independently reads all 294 lines of the canonical solution, checks the original target, and reconstructs the exact certificate. It does not rely on the submitted AI review. Repository integration, CI, generated PDFs, and historical-priority claims are outside this bounded mathematical audit.

## Original target and disposition

The existing question at `linear-systems-and-elimination/IE-05/README.md:40` asks whether the specified positive-diagonal QR factor of the all-minus-one unit lower triangular matrix attains the orthogonal PP supremum for every dimension. The right-hand candidate uses first-available-row ties; the left supremum includes all admissible PP paths. A single admissible orthogonal witness exceeding the candidate at n=8 disproves this universal equality. It need not determine the actual supremum or asymptotics. The negative-resolution notice and scope paragraph make these limits explicit (`README.md:24`; `solution.md:292`). “Solved” is appropriate for this yes/no target, with the retained original statement.

The entire README from `## Context and notation` onward is byte-identical to origin/main `d8cc1134bc5b6c288b9841995e26daf411c8941e`; SHA-256 of that unchanged suffix is `555a8e9222c6b238edd0d2c46efb70a7dcc5f85939592e4f90e409118d9ec8f7`. ID IE-05 and its canonical path are retained.

## Independent exact certificate

I manually transcribed both printed integer matrices and diagonal norm arrays, plus the printed witness T, into `pr127-exact-check.py`. That script uses only Python integers and `fractions.Fraction`; it imports or executes no submitted code. Its complete exact output is `pr127-exact-check.json`.

1. Both integer Gram products are exactly the printed positive diagonal matrices (`solution.md:48–75`, `202–221`). Thus both positively column-normalized matrices are real orthogonal.
2. Forward substitution independently reconstructs upper triangular factors U satisfying H=L U, with positive diagonals. The witness U equals every entry of the printed T. The candidate diagonal is exactly `(1,8,31,106,341,1024,1,5462)`.
3. As an independent QR cross-check, exact rational Gram-Schmidt applied directly to each lower triangular input yields vectors that are positive scalar multiples of the printed columns. Their squared norms match the corresponding scalar-squared times D. This directly verifies the positive QR convention, independently of the displayed LU certificate. Algebraically H=L T gives L=(H D^(-1/2))(D^(1/2) T^(-1)), whose triangular diagonal is positive (`solution.md:116–119`).
4. The checker performs direct successive Schur complements of the raw integer-column matrices. Positive fixed column normalization preserves within-column pivot comparisons and elimination multipliers; an active entry in original column j has exact squared magnitude raw_entry^2/D[j]. The first available row is a maximum at all 8 stages for each matrix; all 56 strict-lower multipliers match the designated lower triangular inputs. No row exchanges are made.
5. All 408 active entries are independently compared against the reconstructed trailing L/U product. Every stage maximum and witness maximum location match the printed tables (`solution.md:174–183`, `249–258`), including the nonfinal input maximum `(3,3)` for the candidate. Thus this checks the full active-Schur-complement definition of growth, not only the final U.
6. The exact results are rho(witness)=5272/63 and rho(candidate)^2=17948132/2601. Their squared difference is exactly `117335164/1147041 > 0` (`solution.md:283–285`). Both growth factors are positive, proving the strict comparison.

The submitted `verification/verify_ie05.py` and `verification/integer_counterexample.py` were inspected. They contain finite exact arithmetic computations consistent with their descriptions. They were not needed or run for this verdict; the latter writes its neighboring JSON, which this read-only audit avoided.

## Primary source check

Primary source accessed directly: https://arxiv.org/html/2308.16146v2 . Section 1.2 specifies real matrices, PP maximum-column pivots, and QR with positive triangular diagonal. Section 3.1, Proposition 2, defines the same Q_n from L_n; Corollary 4 gives its asymptotic growth. Section 3.2 asks about maximal orthogonal growth. Appendix B explicitly states the exact extremizer equality conjecture and distinguishes maximizing the growth numerator from optimizing its denominator. These are the correct source and scope for IE-05; the witness can have a smaller numerator than Q_8 while a sufficiently smaller input maximum gives larger growth. The source also separately conjectures the asymptotic constant in Section 3.2. No external theorem is required to certify this finite counterexample.

Source URL: https://arxiv.org/html/2308.16146v2
Publication link cited by manuscript: https://doi.org/10.1137/23M1597733
