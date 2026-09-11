# IE-14 independent proof review

Review date: 2026-09-11. The full recovered manuscript, its complete in-file preamble, current canonical README, and relevant exact verification code were read independently of the integration agent's reproduction run.

## Verdict and scope

**PASS — full resolution of canonical IE-14. Recommend Solved.** For every `n>=4`, the sharp all-active-entry GEPP growth factor for the complex cyclic tridiagonal pattern with both corners nonzero is `c_n=F_(n+1)+1`. The proof gives an upper bound for every matrix and permitted tie path, and a real rational matrix attaining it for every order.

The provisional identifier matches `linear-systems-and-elimination/IE-14/README.md` exactly: nonsingular complex matrices, ordinary tridiagonal positions plus `(1,n),(n,1)`, both corners nonzero, fixed original ordering, no preliminary permutations, exact maximal-modulus partial pivoting, all ties, and growth over all active Schur entries. No symmetry or diagonal-dominance assumption is added. No mathematical correction or unresolved order was found. This is not a priority certification.

## Reviewed source identity

Source: `.cache/colbrook-recovered/OpenProblemsInNLA_recovered/proofs/IE-14.tex`.

- Full UTF-8/LF SHA-256: `1f67bbf4d5e6e799e73fd15fdc5769e0867779f5800499e170b7b2431cf0b910`.
- Normalized size: **5,942 bytes**.
- Hash procedure: complete UTF-8 decoding, CRLF-to-LF replacement, and UTF-8 re-encoding, without trimming or discarding any header or trailing newline.
- The preamble is included in this hash; no separate common source exists. No submitted or canonical file was edited.

## Complete proof audit

### Theorem 1 and front structure — Sections 1–2, lines 30–42

**PASS.** Scaling the initial maximum to one preserves growth. Before stage `k<=n-2`, there are two old surviving rows drawn from original labels `{1,...,k} union {n}`, and fresh original row `k+1` joins them. All other later rows except original row `n` remain untouched: their earlier original columns are zero, hence they have had zero earlier multipliers and cannot have been chosen as nonzero pivots. Original row `n` must be in the initial front because of the cyclic corner. This accounts correctly for row swaps by original labels rather than current positions.

For old sorted target magnitudes `a>=b` and a zero fresh target value, deleting either old row bounds the survivors by `(a+b,a)`; deleting the fresh target-zero row leaves `(a,b)`, which is also dominated. Here “zero-valued pivot” means zero in the target column, not a zero pivot in the elimination column. Nonsingularity ensures the latter pivot is nonzero. For a general fresh magnitude `c`, the sum of survivor bounds is the sum of all three target magnitudes plus the removed magnitude, hence at most `a+b+c+max(a,b,c)`. These are valid modulus inequalities over the complex field, independent of which allowed GEPP pivot is selected.

### Last column history — Section 3, lines 43–47

**PASS.** The initial old values are at most `(1,1)` from original rows 1 and `n`. Fresh rows 2 through `n-2` have zero in column `n`, giving exactly `n-3` zero-fresh updates before stage `n-2`. Iterating `(a,b)->(a+b,a)` gives `(F_(t+2),F_(t+1))`, so the pair is bounded by `(F_(n-1),F_(n-2))` at that stage.

Fresh original row `n-1` then contributes at most one. Since `F_(n-1)>=1`, the survivor sum is at most `2F_(n-1)+F_(n-2)+1=F_(n+1)+1`. Only these two rows remain. The final elimination updates the last scalar by at most their sum. All preceding target values, including values in removed pivot rows, lie below the same bound. This argument controls the whole active history, not only `U_nn`.

### Ordinary and next-to-last columns — Section 3, lines 48–52

**PASS.** Column 1 contains only initial entries. Column 2 starts with old bounds `(1,0)` and receives a fresh value at most one, so all values before its elimination are at most two.

For `3<=j<=n-2`, the old target entries are zero until stage `j-2`; fresh row `j-1` contributes the first potentially nonzero superdiagonal value. After that update the old pair is at most `(1,1)`. At stage `j-1`, a fresh diagonal value at most one gives survivors at most two. At the stage eliminating column `j`, any new subdiagonal value is at most one. Column `j` is then removed, so there is no additional update to its own active entries. This covers the entire middle-column history. For `n=4` this interval is empty, as it should be.

Column `n-1` is separate because original row `n` contributes from the start. Its initial pair is `(1,0)` and it undergoes `n-4` zero-fresh updates, giving `(a,b)=(F_(n-3),F_(n-4))` before stage `n-3`. This formula correctly gives `(1,0)` when `n=4`; no negative Fibonacci index appears. A fresh value at most one makes the new maximum at most `2a` and its sum at most `2a+b+1=F_(n-1)+1`, because `a>=1`. At the next stage, another fresh value at most one yields any survivor bounded by the larger of the old sum and old maximum plus one. Both are at most `F_(n-1)+1`. At its own elimination column `n-1` has no further new row; the bound is already sufficient. Thus the next-to-last column also stays strictly below the claimed global bound.

Together these cases exhaust every target column and all active stages for every `n>=4`. The initial values `6,9,14,22` follow from the Fibonacci convention in the manuscript.

### Attaining construction — Section 4, lines 53–64

**PASS.** The lower triangular factor is unit diagonal with minus ones on its first two subdiagonals. All diagonal entries of the upper factor are nonzero, including `U_22=1/2` and `U_nn=F_(n+1)+1`; hence `LU` is nonsingular.

For column 1, the only nonzero factor-order entries of `C=LU` are `1,-1,-1` in rows 1,2,3, assigned to original rows 1,`n`,2. These are exactly allowed positions. Column 2 uses `U_12=U_22=1/2`, giving factor-order entries `1/2,0,-1,-1/2` in the first four rows; after assignment they occupy original rows 1,2,3, within the ordinary band. Each later nonfinal column comes from a single diagonal entry of `U` and thus occupies factor-order rows `k,k+1,k+2`, assigned to original rows `k-1,k,k+1` (with truncation at the bottom). All these values have modulus at most one.

The last column multiplication gives `(1,1,0,...,0,1)^T`: the interior cancellations use `F_(i+1)=F_i+F_(i-1)`, while the additional one in `U_nn` creates the last entry. Those factor-order rows 1,2,`n` are original rows 1,`n`,`n-1`, respectively, exactly the allowed locations. Thus the input is cyclic tridiagonal, has maximum modulus one, and has nonzero corners `A_1n=1`, `A_n1=-1`. This remains valid in the smallest case `n=4`, where the position ranges meet but the separate columns do not conflict.

The displayed permutation defines the original matrix rather than imposing a forbidden preliminary reordering. To realize it through ordinary GEPP, select original rows successively according to `sigma=(1,n,2,...,n-1)`. After previous eliminations, active column `k` in factor-row labels has entries `L_ik U_kk`. The intended diagonal has modulus `|U_kk|`, and every other remaining entry has modulus at most that value. Therefore the requested row is an actual maximal-modulus pivot at every stage. Permitted ties suffice; no column swaps are used. The resulting `U_nn` attains `F_(n+1)+1`; the upper proof shows no larger active entry can occur.

## Primary-source alignment

Higham's Problem 9.15(b), printed p. 193, defines the same quasi-tridiagonal pattern by the two nonzero corners and asks for sharp GEPP growth. The ordinary tridiagonal comparison is Theorem 9.11, printed p. 173. The primary source therefore confirms the recovered target, including the meaning of “quasi-tridiagonal.” [Higham, *Accuracy and Stability of Numerical Algorithms*, second edition](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf). The proof's own modulus estimates cover the canonical complex field.

## Supplied code audit

The relevant `verification/checks.py::{cyclic_example,ie14}` and complete `verification/exact.py` were read. The code builds the displayed factors, assigns original rows in the same order, checks the complete forbidden-position pattern and both nonzero corners, then performs actual original-label GEPP. The shared routine checks every selected pivot's active-column maximality and every multiplier, and updates growth using all newly formed trailing entries. The final matrix is compared with the claimed `U`; its nonzero diagonal establishes nonsingularity.

The supplied finite range is `4<=n<=30`, comprising 27 constructions. This reviewer inspected the integration agent's fresh `verification/fresh-results.json`, which records PASS for all 27. These are exact rational checks of the attaining examples, not an exhaustive proof of the universal upper bound; the column-history analysis supplies that part independently.

## Remaining target

None. The sharp constant for every `n>=4` is proved and attained in the exact canonical pivot model. The result is not asserted for complete pivoting, rook pivoting, imposed deterministic tie rules, or preliminary reordered matrices.
