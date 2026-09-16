# IE-14 exact mathematical and numerical target dossier

**Stage:** pre-proof contributor dossier, 15 September 2026. This document is an independent reconstruction of the mathematics and exact diagnostics by the implementation contributor. It is **not** either independent statement-referee approval, a final referee report, or a claim of Lean verification. No IE-14 proof implementation was written during this preparation.

**Permanent target:** `IE-14`, `linear-systems-and-elimination/IE-14/README.md`. The published source base is `d8c38a795876b132c90df8d1be8682d3dcde394c`; its status is **Solved**. All dimensions form one canonical problem. The ID, original statement, source files and existing verifications remain unchanged.

**Attribution:** original resolution by **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization credit is to **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, with substantial OpenAI Codex assistance disclosed. No contact email is introduced. The historical manuscript's original attribution and disclosures are preserved.

## 1. Complete canonical target and source identity

For each integer `n ≥ 4`, let `C_n` consist of nonsingular complex `n × n` matrices whose allowed nonzero positions are exactly the ordinary three tridiagonal bands and the two cyclic corners. In one-based mathematical indexing,

\[
A_{ij}=0\quad\text{if }|i-j|>1\text{ and }(i,j)\notin\{(1,n),(n,1)\},
\qquad A_{1n}\ne0,\quad A_{n1}\ne0.
\]

Positions in the bands may be zero; there is no symmetry, reality, diagonal-dominance, sign, conditioning or genericity restriction. Elimination starts from the given matrix in its given row and column order. At each stage it swaps any maximal-modulus active first-column entry into the first active row and forms the exact trailing Schur complement. Every maximal tie is allowed.

For its `n` active matrices `S_1=A,…,S_n`, define

\[
\rho(A,\pi)=\frac{\max_{1\le k\le n}\max_{i,j}|(S_k)_{ij}|}{\max_{i,j}|A_{ij}|},
\qquad c_n=\sup_{A\in C_n,\ \pi\text{ admissible}}\rho(A,\pi).
\]

The target is the exact **attained** sharp value

\[
c_n=F_{n+1}+1\quad(n\ge4),\qquad F_0=0,\ F_1=1,\ F_{m+2}=F_m+F_{m+1}.
\]

Thus the upper theorem must quantify over all such complex inputs, all admissible tie paths, every active stage, and every active entry. The witness must be provided for every `n ≥ 4`. A final-pivot bound, one deterministic tie rule, real-only theorem, or finite list of dimensions would not settle the target.

The complete retained proof is `references/colbrook-recovered-2026-09-11/manuscripts/IE-14.tex`, Theorem 1 and Sections 2–4, with PDF, submission record, and dated historical review beside it. `reviews/initial/source-hashes.json` records the SHA-256 and byte count of all seven original files used here. In particular:

| Current complete file | SHA-256 |
|---|---|
| Canonical README | `ebbd61a71ba0aa17f4bd076f1f2408e5db63aa3426247b4e4db0bcb0b582d869` |
| Packaged full manuscript TeX | `4c20c2c20e6d05945911883682bc823096ef0ff1011cbd31bf941fd1f309b869` |
| Historical independent review | `409539b6cf58b4bf627c52bb6df6ad2f8833be4a43beb88e591c2fa6b815728c` |

The manuscript preamble and historical review quote `1f67bbf4d5e6e799e73fd15fdc5769e0867779f5800499e170b7b2431cf0b910` for an earlier recovered complete UTF-8/LF source, 5,942 bytes. That is a distinct historical artifact, **not** the hash of the presently packaged 7,141-byte manuscript. No source has been trimmed or rewritten to force these hashes to match. Historical provisional-ID/review-pending text is retained and is contextualized by the later dated packaging and review.

[Higham, *Accuracy and Stability of Numerical Algorithms*, second edition, Problem 9.15(b), printed p.193](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf) asks for sharp GEPP growth for the same two-corner pattern. The adjacent Theorem 9.11, printed p.173, treats complex matrices and supplies the tridiagonal comparison. These pages were checked directly during this preparation; the canonical statement supplies the explicit all-tie and original-order conventions. No new literature-openness or priority claim is made.

## 2. Exact draft definition semantics

This dossier was aligned to the actual typechecked `NLA/IE14/Definitions.lean`, `Challenge.lean`, and seven-name `comparator.json`. The specification build has exactly seven intentional placeholders and establishes no target theorem.

Lean indices are zero-based `Fin n`; source indices are one-based. `Mat n` is `Matrix (Fin n) (Fin n) ℂ`, and `PivotPath n` is `Fin n → Fin n`.

* `rowSwap S k p` sends `(i,j)` to `S (Equiv.swap k p i) j`; columns are fixed.
* `schurStep S k p`, with `B=rowSwap S k p`, has entries `B i j − (B i k / B k k) * B k j` when `k<i` and `k<j`, and zero elsewhere.
* `trajectory A path 0=A`; step `k+1` performs that literal swap and Schur update at `k`. There is no initial permutation. Zero padding is storage for the excluded rows and columns, not an assertion that the entire padded matrix remains nonsingular.
* `AdmissiblePivot S k p` means `k≤p`, `S p k≠0`, and `∀i≥k, ‖S i k‖≤‖S p k‖`. `AdmissiblePath` requires this at **every** `k:Fin n`, including the final scalar stage. Actual complex norms are used. All ties remain admissible.
* `entryMaxNN` is the finite supremum of all entry `nnnorm`s in `ℝ≥0`; `entryMax` is its real coercion. `activeMaxNN S k` restricts both current indices to be at least `k`, contributing zero elsewhere. These are actual entrywise maxima, not matrix operator norms.
* `growth` takes the finite maximum of `activeMaxNN (trajectory A path k.val) k.val` for all `k:Fin n`, then divides by `entryMax A`. The input and final scalar both appear; the subsequently empty padded matrix does not.
* `CyclicInput` states determinant nonzero, every forbidden entry zero, and both corners nonzero. Its corner quantifier uniquely picks `(0,n−1)` under `n≥4`.
* `cyclicGrowthSet n` contains `r` exactly when actual witnesses `A,path` satisfy `CyclicInput A`, `AdmissiblePath A path`, and `r=growth A path`. `sharpConstant` is its real `sSup`; `fibonacciBound n=(Nat.fib (n+1):ℝ)+1`.

The final `IsGreatest` obligation supplies actual membership and an upper bound; its `sSup` conclusion cannot rely on the convention for an empty or unbounded set. Separately, `admissible_path_exists` proves that every nonsingular square complex input has a complete GEPP path, even without cyclic sparsity. This export also includes `n=0`, where the path and all requirements are vacuous. The other semantic maximum export assumes `n≥1` so that a maximizing entry exists.

## 3. Universal front invariant: required full proof

The source's short structural paragraph is substantive. It must be proved from `trajectory`, `rowSwap`, the input support, and admissibility. It is not a new input assumption.

Write source stages as `k=1,…,n−2`; Lean's corresponding stage is `k−1`. Before such a stage there are two old surviving original-row labels from `{1,…,k} ∪ {n}`. Fresh original row `k+1` joins them. Every later original row other than `n` is still unchanged in its remaining active entries. Exactly these three front rows can have a nonzero entry in the current pivot column.

A convenient rigorous invariant uses a permutation `label_k` from current physical row positions to original labels, updated by composition with the actual swap. It must establish:

1. The active labels are the complement of the already selected distinct original labels.
2. Exactly two active labels lie in the old set. Every later label remains active until its prescribed front entry stage.
3. The active entries of a not-yet-entered row equal those of its original input row. Its previous pivot-column entries were zero, so all previous multipliers were zero; swaps only changed its position.
4. The fresh label is distinct from the two old labels. All other active rows have zero in the current pivot column by the original cyclic pattern.
5. An admissible pivot is nonzero, so it belongs to the three-row front, regardless of ties. Swapping and eliminating it leaves exactly two old rows for the next stage.
6. At the final two-row stage no fresh row enters. All earlier removed pivot-row values were counted while active and already obey the relevant bound.

The pivot need not be the largest entry in the **target** column. Its choice is controlled only by the elimination column. Treat each of the three possible removed rows. For every surviving row,

\[
\left|\frac{B_{ik}}{B_{kk}}\right|\le1,
\qquad |B_{ij}-(B_{ik}/B_{kk})B_{kj}|\le |B_{ij}|+|B_{kj}|.
\]

The divisor is nonzero by admissibility, and the estimate uses complex modulus. A source phrase about a “zero-valued pivot” in this argument means a zero **target-column entry of the pivot row**, never division by zero.

For old target magnitudes sorted as `a≥b≥0` and fresh magnitude at most `c`, the source bounds the new sorted pair by `(a+b,a)` when `c=0`, and its sum by `a+b+c+max(a,b,c)` in general. These follow separately in each possible pivot case.

### Equivalent scalar bookkeeping with less sorting

One can avoid introducing a sorted-pair library. Let `M` be the actual maximum of the two old target magnitudes and `T` their sum. For fresh target magnitude at most `c≥0`, each of the three pivot choices yields

\[
M'\le\max(T,M+c),\qquad T'\le T+c+\max(M,c).
\]

When the fresh target entry is zero these give

\[
M'\le T,\qquad T'\le T+M,
\]

using `M≤T`. These scalar consequences retain every source bound needed below. They are an implementation simplification, not a replacement or weakening of the target or a hypothesis on pivot selection.

Nonsingularity/path existence is best handled independently: maintain injectivity of the true active block on vectors supported in active columns. Given a vector in the new Schur kernel, supply its pivot coordinate to obtain an old-kernel vector. The padded matrix's determinant is zero after the first step, so asserting its nonsingularity would be incorrect. A nonzero active column plus finite maximum selection supplies a next legal pivot, inductively producing a complete path.

## 4. Every column and stage, including the smallest order

Let `E=entryMax A`. Under an admissible path with `n≥4`, `E>0` follows already from its first nonzero pivot. The source normalizes `E=1`. A proof may instead carry the common factor `E` in all estimates; this avoids a separate scaling-path equivalence without changing the claim. The following formulas are written in normalized units.

| Target column (one-based) | Complete history and bound |
|---|---|
| `1` | It appears only initially; every entry has modulus at most one. |
| `2` | Old pair starts at most `(1,0)`. The first fresh entry is at most one; the two updated survivors are at most two. The next step removes column 2, so there is no later active column-2 update. |
| `3≤j≤n−2` | Old target values are zero until stage `j−2`. Fresh row `j−1` supplies the first possible nonzero value, giving old maximum at most one and sum at most two. At stage `j−1`, a fresh diagonal entry at most one gives maximum at most two. At the step removing column `j`, the fresh subdiagonal entry is at most one and no subsequent column-`j` update is active. This interval is empty for `n=4`. |
| `n−1` | Initial old bounds are `(1,0)`. After `n−4` zero-fresh updates, maximum is at most `a=F_(n−3)` and sum at most `a+b=F_(n−2)`, with `b=F_(n−4)`. This is `(a,b)=(1,0)` when `n=4`. The next fresh entry at most one gives maximum at most `2a` and sum at most `2a+b+1=F_(n−1)+1`, since `a≥1`. One more fresh entry at most one gives maximum at most `max(2a+b+1,2a+1)=F_(n−1)+1`. At its own elimination there is no additional fresh row. |
| `n` | Initial old maximum is at most one and sum at most two. Fresh original rows `2,…,n−2` have last entry zero, giving exactly `n−3` zero-fresh updates. After `t` such updates the maximum is at most `F_(t+2)` and sum at most `F_(t+3)`. Before stage `n−2`, these are `F_(n−1)` and `F_n`. Fresh row `n−1` has target modulus at most one. The survivor sum is at most `F_n+1+F_(n−1)=F_(n+1)+1`. Only two rows remain, so the last Schur scalar is bounded by that sum. Earlier target values and removed pivot rows obey the same global bound. |

At every listed stage the unentered rows still have input entries of modulus at most one. Thus the front bounds also cover entries outside the front. At every fixed target column, stop its history as soon as that column leaves the active block. Combining these cases covers all active `i,j,k` in `all_active_entries_bound`, not only the diagonal or last column.

In zero-based indexing, the last-column zero-fresh updates are steps `0,…,n−4`; the fresh row with label `n−2` enters at step `n−3`; the final two-row elimination is step `n−2`, and the last scalar occurs in `trajectory … (n−1)`. The `n=4` case has one last-column zero-fresh update and zero next-to-last-column zero-fresh updates. No negative Fibonacci index is used.

## 5. Exact all-size rational witness and actual swaps

In one-based notation, let `L` be unit lower triangular with `−1` on its first two subdiagonals and zero elsewhere. Let `U` be upper triangular with

\[
U_{11}=1,\quad U_{12}=U_{22}=\tfrac12,\quad U_{ii}=1\ (3\le i\le n-1),
\quad U_{i,n}=F_{i+1}\ (i<n),\quad U_{n,n}=F_{n+1}+1,
\]

and every other nonfinal off-diagonal entry zero. Set `C=L U` and assign the original input rows by

\[
C_{i,:}=A_{\sigma_i,:},\qquad\sigma=(1,n,2,\ldots,n-1).
\]

`factorIndex` is the inverse row-label assignment. In zero-based form it is `0↦0`, `n−1↦1`, and `i↦i+1` otherwise; `witnessMatrix i j=(L*U)(factorIndex i)j`. This constructs the input `A`. It does not apply a preliminary permutation to an already given matrix.

The entry calculation has four cases:

* Column 1 of `C` is `(1,−1,−1,0,…)`, assigned to original rows `1,n,2`.
* Column 2 of `C` is `(1/2,0,−1,−1/2,0,…)`, assigned to original rows `1,n,2,3`; its second factor-row value is zero.
* A nonfinal column `j≥3` has entries `1,−1,−1` in factor rows `j,j+1,j+2`, truncated at the bottom. Their original rows are `j−1,j,j+1` where present.
* The last column of `C` is `(1,1,0,…,0,1)`, by the Fibonacci recurrence and the additional final one. Its nonzero original rows are `1,n,n−1`.

Consequently all forbidden entries vanish, all input moduli are at most one, and `A_(1,n)=1`, `A_(n,1)=−1`; hence the exact input maximum is one. The nonzero diagonals of triangular `L,U` prove `det C≠0`, and a row permutation preserves nonvanishing. No expanded `n×n` determinant is needed. The optional exact diagnostic identity is

\[
\det A=(-1)^{n-2}\frac{F_{n+1}+1}{2};
\]

proving this sign formula is not an extra public obligation.

The frozen `witnessPath` chooses physical row `0` at step `0` and physical row `n−1` at every later step. This is **not** an instruction to find a row by its original label. The legal current-position swaps themselves must be proved to produce original pivot labels `(1,n,2,…,n−1)`.

A useful exact trajectory invariant is the factor-row label `f_k(i)` of each active physical row:

* At stage `k=0`, it is `factorIndex i`.
* At stages `1≤k≤n−1`, for active `i≥k`, it is `k` when `i=n−1`, and `i+1` otherwise.

Then for active `i,j≥k`, the literal trajectory satisfies

\[
S_k(i,j)=\sum_{a=k}^{n-1}L_{f_k(i),a}U_{a,j}.
\]

At the chosen pivot row, `f_k(p)=k`. Upper triangularity reduces the active pivot column to `L_(f_k(i),k) U_(k,k)`. Since the chosen lower-factor coefficient is one and all other lower-factor moduli are at most one, the actual chosen pivot is nonzero and maximal, including every tie. The Schur update removes exactly the `a=k` contribution; the physical swap gives the next `f_(k+1)`. This proves actual-path legality rather than merely the existence of some factorization order.

The last scalar is exactly `U_(n,n)=F_(n+1)+1`. Together with the universal all-active-entry upper bound and input maximum one, it establishes the frozen exact growth equality.

For `n=4`, the actual input is

\[
A=\begin{pmatrix}
1&1/2&0&1\\
-1&-1&1&0\\
0&-1/2&-1&1\\
-1&0&0&1
\end{pmatrix}.
\]

The zero-based pivot positions are `(0,3,3,3)`, original pivot labels are `(1,4,2,3)`, pivots are `(1,1/2,1,6)`, and `det A=3`. The exact diagnostic output retains every active matrix for this boundary case.

## 6. Numerical certificate and finite diagnostics

The proposed LeanCert theorem is exactly

`(0 : ℝ) < 1/2 ∧ (1/2 : ℝ) ≤ 1`.

Prove its two scalar obligations with explicit `interval_decide (trust := kernel)` calls and assert kernel trust. Its strict lower bound must be used in the witness's half-pivot nonvanishing; its upper bound must be used when bounding the input half entries. The real facts transfer to the rationally embedded complex coefficients via actual complex norm/cast lemmas. Keep the named certificate on the witness theorem's dependency path. The certificate is not a numerical substitute for the symbolic all-size Fibonacci/front argument.

`reviews/initial/exact-check.py` is a new Python standard-library `Fraction` checker, separate from the retained historical verifier and prior reconnaissance checker. It checks every dimension `4,…,30`, all 27 passing. For each dimension it:

1. Constructs the exact `L,U` using the frozen definition branch order, multiplies them, and assigns input rows with `factorIndex`.
2. Checks the full forbidden-entry pattern, both actual corners, and initial maximum one.
3. Computes the determinant independently by ordinary elimination with first-nonzero pivots, without using the prescribed path or triangular determinant formula.
4. Starts the actual GEPP trajectory from `A` and uses only `p=k` for `k=0`, otherwise `p=n−1`. Original row labels are recorded solely as observations and never determine the chosen pivot.
5. Checks every prescribed pivot's active-column maximality and nonvanishing, every multiplier bound, every active entry against the claimed bound, and the complete factor-residual identity at every stage in physical row order.
6. Performs the literal row swap and padded Schur update; verifies the pivot-row records reconstruct `U`, the observed original-label sequence is `σ`, the final scalar and peak growth equal `F_(n+1)+1`, and the final extra update is the all-zero padded matrix.

The first four growth values are `6,9,14,22`; at `n=30` the growth is `1346270` and the determinant is `673135`. All arithmetic is exact rational arithmetic, with no floating-point tolerance or rounding. These finite diagnostics do **not** prove the universal upper bound, all complex tie paths, or the all-size witness. They detect transcription and physical-path/indexing errors before proof implementation.

## 7. Exact correspondence with the seven draft exports

All names are in namespace `NLA.IE14`; the actual `Challenge.lean` signatures and `comparator.json` are authoritative. No exported hypothesis may be strengthened or conclusion weakened during implementation.

| Export | Exact semantic obligation |
|---|---|
| `numerical_bounds` | The conjunction `0 < (1/2:ℝ)` and `(1/2:ℝ) ≤ 1`, consumed as described above. |
| `entryMax_semantics` | For every natural `n`, `hn:1≤n`, and complex `A:Mat n`: `0≤entryMax A`, every actual entry norm is at most that value, and actual indices `i,j` attain it. |
| `admissible_path_exists` | For every `n` and every complex `A:Mat n` with `A.det≠0`, there exists `path:PivotPath n` satisfying the full `AdmissiblePath A path`. No sparsity or dimension restriction. |
| `all_active_entries_bound` | For every `n≥4`, every `A` with `CyclicInput A`, and every `path` with `AdmissiblePath A path`, for every `k,i,j:Fin n` with `k≤i` and `k≤j`: `‖trajectory A path k.val i j‖ ≤ fibonacciBound n * entryMax A`. |
| `witness_data` | For every `n≥4`, the literal `witnessMatrix n hn` satisfies `CyclicInput` and its literal `entryMax` equals one. |
| `witness_attainment` | For every `n≥4`, the literal `witnessPath n hn` is admissible for the literal witness input, and its literal `growth` equals `fibonacciBound n`. |
| `canonical_result` | For every `n≥4`, `IsGreatest (cyclicGrowthSet n) (fibonacciBound n)` **and** `sharpConstant n=fibonacciBound n`. Membership comes from the fully verified witness; the upper half comes from all active entries on every path. |

No optional determinant sign, finite diagnostic, front invariant, or scalar envelope is being substituted for one of these seven targets. Those are auxiliary obligations supporting the full exports.

## 8. Pinned APIs, reusable patterns and new obligations

The checked pins are Lean `v4.33.1`, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. `reviews/initial/APIProbe.lean` contains imports and `#check` commands only; it typechecks successfully under those pins. Its output records exact signatures. No Lean lemma or proof was implemented by this probe.

* **Finite maxima:** `Finset.le_sup`, `Finset.sup_le`, `Finset.exists_mem_eq_sup`, `Finset.exists_max_image`, `NNReal.coe_le_coe`, `coe_nnnorm`. Prove these custom maxima correspond to the intended modulus maxima, then pass entry bounds to stage and whole-run bounds.
* **Complex multipliers:** `norm_pos_iff`, `norm_div`, `norm_mul`, `norm_sub_le`, `div_le_one`, `div_le_iff₀`, `Complex.norm_real`. The existing IE-05/IE-15 real absolute-value arguments require explicit adaptation, not an implicit change of field.
* **Fibonacci:** `Nat.fib_zero`, `Nat.fib_one`, `Nat.fib_add_two`, `Nat.fib_add_one`, `Nat.fib_mono`, `Nat.fib_pos`; cast their natural identities/order statements into nonnegative real envelopes and into complex witness entries. Avoid a large computed table as a surrogate for induction.
* **Literal swaps:** `Equiv.swap_apply_left`, `Equiv.swap_apply_right`, `Equiv.swap_apply_of_ne_of_ne`, `Equiv.swap_apply_self`. The original-label front and actual witness label maps are new proof work; no ready cyclic-front theorem was found.
* **Path existence:** `Matrix.isUnit_iff_isUnit_det`, `Matrix.mulVec_injective_iff_isUnit`, `Matrix.mulVec_single_one`, `Matrix.mulVec_add` support active-block injectivity on supported vectors. The actual IE-05 `GEPP.lean` contains the corresponding real proofs `activeInjective_initial_proved`, `activeInjective_nonzero_column_proved`, `activeInjective_rowSwap_proved`, `schurStep_mulVec_proved`, and `activeInjective_schur_proved`. Their algebraic argument adapts to complex vectors. Finite maximum selection and a recursive trajectory still need to be connected to the frozen path definition.
* **Triangular witness nonsingularity:** `Matrix.det_mul`, `Matrix.det_of_isUpperTriangular`, `Matrix.det_of_isLowerTriangular`, `Finset.prod_ne_zero_iff`, and row-reindexing `Matrix.det_permute`. Check the actual latter signature: the first submatrix map acts on row indices, despite its current source docstring describing columns. Its sign factor is a unit, so an explicit parity computation is unnecessary. `Matrix.det_fromBlocks₁₁` exists as an alternative Schur determinant route, but supported-vector injectivity avoids changing active-block index types.
* **Trailing product identity:** `Matrix.mul_apply`, `Finset.sum_eq_single`, `Finset.sum_add_distrib` suffice for a symbolic tail sum. IE-05 `LUTrajectory.lean` supplies real no-swap `tailProduct_pivot_row`, `tailProduct_pivot_column`, `tailProduct_split`, and `scaled_tail_schur` patterns; IE-14 must additionally prove the physical row permutation at each stage. IE-15's `Permutation.lean` gives related trailing-reindex patterns, but its pivot rule is rook pivoting with column swaps and cannot be reused as the IE-14 semantic theorem.
* **Sharp value:** `IsGreatest.isLUB`, `IsLUB.csSup_eq`, `le_csSup`, `csSup_le`. The exact attaining matrix/path proves nonemptiness; the universal bound proves boundedness. No completeness shortcut without those facts is intended.

The largest outstanding formal work is the all-tie original-label/front induction and its column-history indexing, rather than numerical computation or a missing external analytic theorem. The source argument appears mathematically complete on this contributor reconstruction, subject to independent review and actual kernel implementation. In particular, none of these structural facts has already been proved merely by the draft's successful typecheck.

## 9. Review, trust and publication conditions

Before proof implementation, two independent non-implementing referees must review the exact definition, statement, dossier, diagnostic and dependency bytes, and the coordinator must commit the approved boundary. Subsequent proofs must retain full canonical correspondence and use no custom axioms, `sorry`, `admit` or `native_decide` in the solution closure. `Challenge` placeholders are specifications only and must not be imported as solutions.

The eventual seven target declarations require explicit kernel trust assertions and axiom reports; Comparator permits only `propext`, `Classical.choice`, and `Quot.sound`. Fresh reproducible verification, independent final review, truthful metadata, and the separate problem PR precede any canonical **Lean verified** promotion. This dossier supplies none of those later approvals or results.

## 10. Portable reproduction

When the coordinator retains these files under the IE-14 Lean project, use:

```bash
python3 reviews/initial/exact-check.py > /tmp/ie14-exact-results.json
cmp reviews/initial/exact-results.json /tmp/ie14-exact-results.json
python3 reviews/initial/exact-check.py --source-hashes-output /tmp/ie14-source-hashes.json > /tmp/ie14-exact-results.json
cmp reviews/initial/source-hashes.json /tmp/ie14-source-hashes.json
lake env lean reviews/initial/APIProbe.lean
```

The checker discovers its enclosing repository by walking parents for `problem_ids.json` and validates the permanent `IE-14` mapping. An external staging invocation can pass `--repo-root PATH`; no absolute development path is embedded in the script or output. All seven source hashes and numerical results are independent of checkout location. The API probe is read-only except for normal compiler/cache behavior and has no proof declarations.
