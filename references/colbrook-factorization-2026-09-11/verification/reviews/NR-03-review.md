# NR-03: independent mathematical review

Reviewer: independent agent `/root/review_transfer_counterexamples`, 2026-09-11.

**Verdict: PASS for the exact statement `rank_+(C_3)=8`; PARTIAL resolution of canonical NR-03.** No substantive gap was found. The proof does not establish the universal family assertion for every `n>=3`.

## Reviewed material and immutable identity

Read the entire original manuscript `.cache/colbrook-all-submission/nla_submission/manuscripts/NR-03_n3_exact_rank.tex`, including its locally defined preamble, all proofs, verification claims, and limitations; the full canonical `nonnegative-and-positive-factorizations/NR-03/README.md`; and the submitted diagnostic `verification/verify_nr03_n3.py`. The manuscript has no external preamble dependency. No original proof or canonical statement was edited.

SHA-256 over the **complete** UTF-8 source after CRLF-to-LF conversion, with no whitespace trimming or final-newline removal:

`6b011818e6e430346073f47a875e344c78217f2b1bbce5788bacd29787ab751e`

Normalized length: **5631 bytes**. The source in this extraction already used LF.

## Exact statement and primary-source match

Theorem 1 (`thm:main`, source line 17) fixes the full eight-by-eight matrix, including the entry 4 at intersection size three. Identifying a subset with its indicator vector maps this matrix exactly to the canonical `C_n(a,b)=(1-a^T b)^2` at `n=3`. Nothing is left unspecified or treated as a partial unique-disjointness completion.

The rank in both texts is exact **real nonnegative rank**: arbitrary real nonnegative factors are allowed. Rationality, integrality, symmetry, a prescribed factor support, and finite-precision approximation are not additional assumptions in the lower bound.

The original all-order conjecture appears in §6.4, Conjecture 4 of [Vandaele–Gillis–Glineur–Tuyttens, *Heuristics for Exact Nonnegative Matrix Factorization*](https://arxiv.org/html/1411.7245). [Baeckelant–Vandaele–Gillis v2](https://arxiv.org/html/2605.14058v2), Appendix A.4 Table 9, lists lower/upper values 7/8 for `n=3`. These primary texts confirm the manuscript addresses a real finite-case gap within the larger canonical conjecture.

## Proof audit

### Ordinary rank and parity identities — §2, lines 26–49

PASS. Independently regenerated all 64 entries from bit-mask intersection cardinalities and checked them against the printed matrix. The printed vector is exactly `z_A=(-1)^|A|`. Integer multiplication gives both `Cz=0` and `z^T C=0`. Exact rational elimination gives determinant **-8** for the leading seven-by-seven principal block. The nonzero minor gives rank at least seven and the nonzero null vector gives rank at most seven, so the ordinary rank is exactly seven.

For a hypothetical inner dimension seven, both factors must have ordinary rank seven, because their product does. Hence `W:R^7 -> R^8` is injective, giving `Hz=0`. Similarly `H:R^8 -> R^7` is surjective (or has a right inverse), so `z^T W H=0` gives `z^T W=0`. Each column of `W` and each row of `H` is consequently parity balanced. A nonzero nonnegative balanced vector must have a positive coordinate of each parity. All these deductions hold for arbitrary real entries.

Nonnegativity implies that every zero of `C` is a zero in every summand. Therefore a summand's positive support is a rectangle wholly inside the positive support of `C`. There is no cancellation loophole.

### Restricted nine-entry lemma — Lemma 2, `lem:nine`, lines 59–70

PASS. The nine specified entries are distinct and all equal one. I checked all types of pairs, including the mixed types for different indices.

- For different indices, pairs of type `(s_i,d_i)` and `(s_j,d_j)` have a zero cross-entry `C(s_i,d_j)`. Pairs of the transposed type have `C(d_i,s_j)=0`. Mixing these two types gives the zero cross-entry `C(d_j,d_i)=0`. A pair involving `(d_i,d_i)` similarly has one of these three zero types. Thus every pair with different indices is forbidden in a positive rectangle.
- At a fixed index, `(s_i,d_i)` and `(d_i,s_i)` are incompatible because their cross-entry `C(s_i,s_i)` is zero.
- If one rectangle contains `(s_i,d_i)` and `(d_i,d_i)`, a column index in its support must avoid `i` and cannot intersect the complementary doubleton in exactly one point. Its only possibilities are the empty set and `d_i`. Both have even parity, contradicting the necessary odd positive coordinate in the row vector `h`.
- The remaining pair is the transpose of the preceding case and uses parity balance of the column vector `w`.

This exhausts all unordered pairs of distinguished entries. The lemma is a restriction for parity-balanced summands, not an ordinary unrestricted fooling set of size nine.

### Main conclusion — proof after Lemma 2, lines 72–74

PASS. In a seven-term nonnegative sum, every distinguished positive entry must be positive in at least one term. The lemma permits at most one such entry per term, making seven terms insufficient for nine entries. Factorizations of inner dimension below seven were already excluded by ordinary rank. The trivial identity factorization `C=C I_8` has eight nonnegative terms. Thus the exact conclusion is `rank_+(C_3)=8`.

The apparent nine-versus-eight counting issue is correctly handled in §4: parity balance was obtained only under the seven-term hypothesis. For wider factorizations, `W` need not be injective and `H` need not have full row rank, so the restrictions cannot be carried over. The explicit eight-term factorization is therefore consistent with the proof.

## Independent computation and limits of diagnostics

I implemented a separate exact-arithmetic check using Python standard-library `fractions.Fraction`, without importing or executing the submitted checker. It regenerated the matrix and null vector, verified both null identities, found rank seven and minor -8, and directly enumerated all row/column support pairs containing both parities. There were **89** positive-support rectangles; the maximum number of distinguished entries in any was **1**, matching the manuscript.

This enumeration checks a necessary support condition for the hypothetical balanced factors. It does not pretend to solve a real nonlinear optimization problem or infer infeasibility from a floating-point solver. The symbolic proof provides the link from every possible seven-term factorization to the enumerated class. The submitted checker was read and implements the same claimed finite checks consistently.

## Remaining cases and disposition

- The `n=3` case has a complete proof in this candidate, with no unresolved exceptional factor configuration.
- The exact family question `rank_+(C_n)=2^n` for **every `n>=4`** is not answered by this manuscript. No induction, tensorization, or other valid propagation mechanism is supplied.
- The base-case argument cannot be relabeled a full resolution of NR-03. It is suitable as independently reviewed partial evidence, with the infinite family retained as unresolved.
- The proof establishes exact real nonnegative rank, and does not claim robustness for approximate factorizations, a numerical separation margin, or a new unrestricted rectangle-covering number.
- Bibliographic novelty and priority against all subsequent work are not certified by this bounded primary-source and proof review. PASS denotes analytic review of a candidate, not journal acceptance or formal verification.
