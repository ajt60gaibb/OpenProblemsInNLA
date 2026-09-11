# IE-13 independent proof review

Review date: 2026-09-11. The complete recovered manuscript and its in-file preamble, current canonical README, and relevant exact verification code were read independently of the integration agent's reproduction run.

## Verdict and canonical scope

**PASS — full resolution of canonical IE-13. Recommend Solved.** The sharp dimension-independent bound is `G(0,q)=1`, and for `p>=1` it is `G(p,q)=h_(p+q)`, where `h_t=0` for `t<=0` and `h_t=1+sum_(r=1)^p h_(t-r)` for positive `t`. The proof supplies an upper bound for every complex nonsingular matrix of the permitted bandwidths and every allowed GEPP tie choice. A real rational matrix attains the bound at order `2p+q+1`. Thus every unequal pair, including one zero bandwidth, is covered; the manuscript also recovers the already-known equal-bandwidth case.

The provisional recovered identifier matches the actual `linear-systems-and-elimination/IE-13/README.md`. Both use exact GEPP in fixed original column order, maximal-modulus active-column pivots, no preliminary reordering, bandwidths **at most** `p,q`, and growth over **all active Schur-complement entries**. The canonical restriction `n>=1+max(p,q)` is satisfied by every attaining construction, while the upper proof applies even without that lower bound on order. No mathematical correction or remaining canonical case was found. No publication-priority claim is made.

## Source identity

Source: `.cache/colbrook-recovered/OpenProblemsInNLA_recovered/proofs/IE-13.tex`.

- Complete UTF-8/LF SHA-256: `cb114fce65650805c214f7131bc325f15a2bf860009f79bde43ad7de7558bf9b`.
- Normalized size: **7,237 bytes**.
- Normalization: decode the complete file as UTF-8, replace CRLF by LF, and re-encode. No trimming, header removal, or removal of terminal newlines.
- The complete preamble is included in this hash; there is no separate common source. No proof or canonical file was modified by this reviewer.

## Proof audit

### Theorem 1 and recurrence identities — Section 1, lines 30–46

**PASS.** Scaling a nonzero nonsingular matrix to maximum modulus one leaves the growth factor unchanged. For `p=0`, the matrix is upper triangular, its diagonal is nonzero, and all elimination multipliers are zero; growth is exactly one, including `q=0`.

For `p>=1`, the recurrence is well defined and nondecreasing. Up to `t=p+1`, it gives `h_t=2^(t-1)`. This proves `G(p,0)=2^(p-1)`. Substitution/induction beyond that range gives the displayed formula for `1<=q<=p+1`; in the `q=1` endpoint the coefficient `q-1` is zero, so the negative power `2^(q-2)` causes no issue. For `p=1`, `h_t=t`; for `p=2`, `h_t=F_(t+2)-1`. Thus the quoted specializations, including equal bandwidth, agree with the recurrence.

### Sorted-front lemma and envelope state — Section 2, lines 47–62

**PASS.** If the removed entry has magnitude `y_a`, each survivor is bounded by `y_a+y_i`. Those bounds are already ordered as the original sorted entries with `y_a` removed. At survivor position `i<a`, the desired inequality reduces to `y_i-y_(i+1)<=y_1-y_a`, which follows because the latter telescoping sum includes the former nonnegative gap. At positions `i>=a`, use `y_a<=y_1`. This establishes coordinatewise domination by the result of deleting the largest target magnitude. It does **not** assume that GEPP actually chooses its pivot by this target column.

Sorting and appending a fresh bound are monotone. Starting with `p` zero entries, the first fresh unit entry produces `p` ones. Thereafter all entries of the canonical state are at least one, so appending a one gives the ordered front used in the displayed update. The transformed sequence `(x_1+x_2,...,x_1+x_p,x_1+1)` is itself ordered because `x_p>=1`.

The explicit formula `x_i^(t)=1+sum_(r=1)^(p-i+1) h_(t-r)` satisfies the initial all-ones state and the update: adding the prior largest entry `h_t` to `x_(i+1)^(t)` shifts the sum exactly as required. Its first entry is `h_t` by the recurrence. For `p=1`, the state has one entry and the update is simply `x_1+1`, also covered.

### Every active column and arbitrary orders — Section 3, lines 63–66

**PASS.** At the start of stage `k`, original rows with labels `i>=k+p` have zeros in all earlier original columns. Inductively they have had zero multipliers and remain untouched; a zero entry cannot be selected instead of a nonzero maximal pivot in an active column of a nonsingular matrix. Among the earlier row labels there are at most `p` surviving rows, with original row `k+p` the next fresh candidate. This is a statement about original labels, so actual row swaps do not invalidate the front description. Near the bottom, missing candidates can be padded with zero bounds.

For target column `j>=p+q+1`, the first original row which can have a nonzero target entry is `j-q`. It arrives at stage `k_0=j-p-q`. Before that stage, all relevant old target values are zero and previous pivot rows have zero in the target column, so no earlier fill can arise there. There are exactly `p+q` updates from `k_0` through `j-1`. Each fresh original target entry is at most one. The sorted-front envelope therefore bounds the surviving old values by `h_(p+q)` before column `j` is eliminated. Fresh and untouched entries remain at most one, and all earlier pivot-row target entries obey the same nondecreasing envelope.

For `j<=p+q`, the initial old magnitudes are bounded by the all-ones state obtained after one imaginary update. At most `j-1` actual updates occur before column `j` is eliminated; the bound is `h_j<=h_(p+q)`. This avoids assuming that the target column initially vanishes in early columns. It also covers orders shorter than a fully populated front. Applying the reasoning to every target column bounds all active Schur entries, not merely final entries of `U` or the selected pivots.

The argument uses modulus and the triangle inequality only, so it applies over the complex field and to all ties, cancellations, and additional structural zeros.

### Attainment: support, normalization, pivot choices, and nonsingularity — Section 4, lines 67–95

**PASS.** Let `j=p+q+1`, `n=j+p`, and `sigma=(p+1,1,...,p,p+2,...,n)`. The permutation defines the original matrix by `A=P^T L_0 U` in the specified first columns; it is not an instruction to reorder the input before GEPP.

For `k<=p+1`, the displayed vector has `u_1=1`, `u_i=2^(i-2)` for `2<=i<=k`, and zeros afterwards. Multiplication by the first `p` subdiagonals of `L_0` cancels entries `2,...,k`. Its first entry remains one, and subsequent entries are negatives of consecutive subsets of those nonnegative coefficients. Their magnitudes are at most the stated `2^(k-1)<=2^p`. Under `P^T`, the surviving support falls in original rows `k,...,k+p`; in particular the nonzero first factor-order row becomes original row `p+1`, which is in this interval. For `k>=p+2`, `L_0 e_k` has support `k,...,k+p`, where the row permutation is already the identity. Multiplication by `eta=2^-p` bounds all these entries by one.

The target column has ones exactly in original rows `p+1=j-q` through `n=j+p`; all its entries respect both bandwidth bounds. Later identity columns do as well. The target column establishes initial maximum modulus exactly one. The construction is real and rational.

The first `j-1` columns admit the intended triangular factorization with nonzero diagonal pivots. At stage `k`, after selecting the preceding rows of `sigma` and performing actual elimination, the residual entries in column `k` are `L_(0,ik) U_kk` in the remaining factor-order rows. The intended pivot has multiplier one and every competitor has multiplier modulus at most one. Hence selecting the next original row of `sigma` is an admissible GEPP row interchange. No column permutation or prohibited initial row permutation is used. Exact ties are allowed by the canonical statement.

For the target column, `c_1=1`, `c_2=...=c_(p+1)=0`, and later `c_i=1`. Forward substitution gives `u_1=1` and `u_i=h_(i-1)` for `i>=2`: through `p+1` the leading one in the recurrence comes from `u_1`, and afterwards it comes from `c_i`. Thus the active entry at stage `j` in the next factor-order row is `h_(p+q)`.

The original first `j` rows are exactly the factor-order first `j` rows, up to permutation. Their leading block has the nonzero first `j` factor pivots, including the positive target value. All later columns of the original matrix are identity columns, with zeros in the first `j` rows. Consequently the original matrix is block lower triangular with nonsingular leading block and identity trailing diagonal block. It is nonsingular. The upper proof prevents later elimination from exceeding the bound already attained. These observations include `q=0` and `p=1`.

## Primary-source alignment and code audit

Higham's Problem 9.15(a), printed p. 193, asks for sharp GEPP growth for lower bandwidth `p` and upper bandwidth `q`. Theorem 9.11, printed p. 173, supplies the complex equal-bandwidth comparison. The recovered question and present canonical formulation match those sources. [Higham, *Accuracy and Stability of Numerical Algorithms*, second edition](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf). Source alignment is not a claim that later literature has been exhaustively searched.

The relevant `verification/checks.py` functions `band_bound`, `band_example`, and `ie13`, and the complete shared `verification/exact.py`, were read. The construction matches the proof. The GEPP verifier tracks original row labels, performs each actual row swap, checks its maximal modulus, and records newly updated trailing entries. Its requested `j-1` steps suffice to witness the stage-`j` active target entry. The separate exact determinant check establishes nonsingularity. It intentionally does not implement or prove an exhaustive all-matrices upper bound; that is supplied by the proof above.

The supplied finite suite covers 60 constructions (`1<=p<=6`, `0<=q<=9`) and the recurrence identities over additional finite ranges. This reviewer inspected the integration agent's fresh `verification/fresh-results.json`, which records PASS for all 60 constructions. Finite successful examples corroborate the formulas but do not replace the all-order argument.

## Remaining target

None. The least universal bound is proved and attained for every required parameter pair. A result for deterministic implementation-specific tie rules or for preliminary bandwidth-reducing reorderings is not claimed and is outside the canonical target.
