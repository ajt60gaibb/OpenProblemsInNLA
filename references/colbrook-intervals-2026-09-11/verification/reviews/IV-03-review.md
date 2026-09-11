# IV-03 independent proof review

Review date: 2026-09-11. Verdict: **PASS — full canonical target, with a stronger one-sign characterization.** Recommend **Resolved** for IV-03, with attribution to the submitted manuscript and this independent mathematical audit. No mathematical correction is required. This is a Codex proof audit, not journal peer review or a priority determination.

## Reviewed source identity and scope

The complete original `.cache/colbrook-package-submission/nla_submission/manuscripts/IV-03.tex` was read, including the abstract, all proofs, complexity discussion, boundary cases, and bibliography. Its included `common.tex` was also read in full. Hash normalization is UTF-8 decoding, replacement of CRLF by LF, then UTF-8 encoding, without trimming or removing the final newline.

| Original source | Normalized bytes | SHA256 |
|---|---:|---|
| `IV-03.tex` | 8725 | `cac971f3f3ef4d54790ca095ace7ba393a2f4ebba00c2f5346a34f7756e5e338` |
| `common.tex` | 985 | `d8e7a0de2ed1a1fd162b147211fe29c7b1d7bfbc0be7b827dcda4d9a2653d0d4` |

The canonical target is `intervals-and-absolute-value-equations/IV-03/README.md`: arbitrary real independent-entry intervals, all dimensions n >= 1, including degenerate intervals, and equivalence between the inverse-M property throughout the interval and the specified 2n² signed vertices. The manuscript proves equivalence using only the n² vertices `C-D_i R D_j`. These belong to the canonical family, so the stronger theorem directly establishes the original target. It does not assert that n² distinct tests are always necessary or optimal.

`common.tex` supplies notation, formatting, and the shared theorem counter; it adds no mathematical assumptions. Numbering is Theorem 1 (`thm:main`, line 15), Lemma 2 (`lem:closure`, line 20), and Lemma 3 (`lem:adj`, line 40). The main proof starts at line 61; complexity and boundary discussion starts at line 103.

## Independent proof checks

### Lemma 2: closure facts — PASS

Starting with a nonsingular M-matrix B, its inverse is nonnegative and invertible, so every row has a positive entry. Thus `w=B^{-1}1` is strictly positive. The scaled matrix `H=B diag(w)` has off-diagonal entries nonpositive and row sums one. Consequently each diagonal exceeds the sum of the absolute off-diagonal entries in its row. Every principal submatrix retains strict row diagonal dominance and positive diagonal. The decomposition `D(I-K)` has K nonnegative with row sums less than one. Its Neumann series proves inverse nonnegativity, and the homotopy `I-tK` proves positive determinant. Scaling back preserves both conclusions.

For A=B^{-1}, Jacobi's complementary principal-minor identity gives positive determinants for every principal block of A, including the full and singleton blocks. In the block inverse formula, `B_ST B_TT^{-1} B_TS` is nonnegative because its two outer factors are nonpositive and its middle factor is nonnegative. Therefore subtracting it from B_SS leaves nonpositive off-diagonal entries. Together with `A_SS >= 0`, this proves the asserted inverse-M principal-block closure. The principal Schur complement of A equals the inverse of B_TT, which proves the last assertion. Empty complementary blocks use the usual determinant-one convention. No irreducibility or entrywise strict positivity is needed.

### Lemma 3: adjugate completion — PASS

This is the essential step preventing circular use of full-matrix regularity. If det A=0, a positive principal minor of order n-1 forces rank A=n-1; hence H=adj A has rank one and strictly positive diagonal. For rank-one H=uv^T, the identity `H12 H23 H31 = H11 H22 H33` follows directly by multiplication. The left side is nonpositive under the assumed off-diagonal signs, while the right side is positive. The argument requires three distinct indices and correctly assumes n >= 3.

If det A<0, the diagonal of B=A^{-1} is negative and its off-diagonal entries are nonnegative. Jacobi's identity makes every nonempty principal minor of B negative: its numerator is a positive proper principal minor of A or the empty determinant one. On any three indices, the negative order-two minors imply `pr>ab`, `qt>ac`, and `su>bc` in the displayed notation. Independently expanding the order-three determinant gives `-abc + a su + b qt + c pr + pst + qru`, strictly larger than `2abc`. That contradicts its negative principal determinant. The lemma does not need A itself to be nonnegative.

The n >= 3 restriction cannot simply be dropped: `[[1,2],[2,1]]` has positive proper principal minors, negative off-diagonal adjugate entries, and determinant -3. The manuscript correctly treats dimension two separately.

### Theorem 1: induction and endpoint monotonicity — PASS

Every lower endpoint L_ij is the (i,j) entry of its tested V_ij, including i=j, so all interval members are nonnegative. For n=1 the test is L>0. For n=2 the tested V_11 has lower diagonal and upper off-diagonal entries; its positive determinant gives a positive determinant lower bound for every A in the box. Positivity of both lower diagonal entries follows from inverse-M closure. The inverse signs then follow from the explicit two-by-two inverse.

Every nonempty proper principal interval inherits all its local tested vertices by restriction of the corresponding global V_ij. Lemma 2 and induction therefore give inverse-M proper principal blocks for every full interval member. This assertion ranges over the entire box and supplies the positivity and nonsingularity required in the subsequent derivatives. It is not an exponential subroutine in the recognition algorithm.

For distinct i,j and S the complementary indices, let `f=a_ij-A_iS A_SS^{-1} A_Sj`. In the proper block on `{i} union S`, the scalar Schur complement is positive by the ratio of principal determinants, and the top-right inverse block equals a negative positive-scalar multiple of `u=A_iS A_SS^{-1}`. Therefore u is nonnegative; the analogous block on `S union {j}` gives `v=A_SS^{-1} A_Sj >= 0`. This is a valid use of proper-block inverse signs, not an assumption about the full inverse.

Differentiating the inverse gives exactly the manuscript's four derivative groups: 1, -v_k, -u_k, and u_k v_l. Thus f is minimized by setting its direct entry and the S-by-S block to their lower endpoints and its two linking blocks to their upper endpoints. These are exactly their entries in V_ij. Changing coordinates sequentially within the box proves this endpoint minimization even when some widths or derivatives are zero. Every intermediate proper block remains invertible. Smoothness locally follows from its positive determinant; boundary points cause no derivative problem.

The resulting `f(A)>=f(V_ij)>=0` uses the nonnegative two-index Schur complement of the tested inverse-M vertex. The off-diagonal adjugate identity is correctly oriented: `(adj A)_ij=-det(A_SS) f_ij(A)`. Eliminating the invertible S block reduces it to the off-diagonal adjugate of a two-by-two matrix. For example, in dimension three `(adj A)_12=a_13 a_32-a_12 a_33`, confirming the index convention. The identity remains valid if the full matrix is singular. All off-diagonal adjugate entries are therefore nonpositive. Lemma 3 now proves det A>0; only at this point does the proof divide by the full determinant. Nonnegativity of A and the inverse signs complete the induction. Necessity follows because all tests are actual interval members.

## Complexity and diagnostic code

Constructing n² rational vertices is polynomial. Each exact inverse and sign test takes cubic arithmetic cost with standard elimination, giving O(n^5) arithmetic operations. Rational elimination can be performed with polynomially bounded intermediate bit lengths using standard exact elimination or fraction-free methods. Clearing rational denominators and applying determinant bounds also shows that all inverse entries have polynomial binary length. The manuscript claims polynomial bit complexity, not a strongly polynomial bit algorithm; this distinction is correct. Arbitrary real inputs are covered by the mathematical equivalence, while the bit claim is explicitly for rational inputs.

The relevant portions of `code/nla_algorithms.py` and `code/verify_exact.py` were read. `inverse_m_exact` uses exactly the stated definition, and `inverse_m_vertices_exact` implements the correct negative-sign family. The verification script exhausts the 1,296 two-by-two boxes with endpoints in {0,1,2}, adds finite rational examples of orders three and four, and checks the dimension-two limitation of the adjugate lemma. These are useful finite diagnostics. Comparing all entry vertices in a higher-dimensional box does not by itself prove the property for every interior point; the written induction supplies that proof. No diagnostic success label was accepted as a substitute for it. Parent-task reruns are recorded separately.

## Primary-source comparison and recommendation

Hladík's [author preprint, §9, Theorem 24 and Conjecture 1, p. 11](https://arxiv.org/pdf/1711.08732) defines exactly these singleton sign vectors and proposes the two-sign vertex characterization. Theorem 24 is an inverse-hull result under an existing inverse-M promise, so it does not already establish recognition. Garloff–Al-Saafin–Adm's [2021 paper, p. 64, paragraph before IP 4.4](https://reliable-computing.org/reliable-computing-28-pp-056-070.pdf) explicitly leaves this conjecture unresolved while establishing a different exponential family. The manuscript's source comparison is accurate.

**Final disposition: PASS for the entire submitted IV-03 manuscript and the full canonical IV-03 equivalence. Recommend Resolved. No remaining portion of that canonical target is left open by this proof.** The review verifies the supplied argument; it is not an exhaustive later-literature or priority search.
