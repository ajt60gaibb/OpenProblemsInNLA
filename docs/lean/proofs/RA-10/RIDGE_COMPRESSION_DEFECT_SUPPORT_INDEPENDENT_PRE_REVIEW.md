# RA-10 selected compression deficit support: independent pre-implementation review

**Disposition:** approve the exact public trace equality as a partial Lemma 2 gate. The coefficient-two ridge positive-part estimate and the frozen RA-10 Target remain open.

I independently checked `RIDGE_COMPRESSION_DEFECT_SUPPORT_PRE_REVIEW.md` at SHA-256 `024504e972c827f4ea68046355c0da0222973d5b87a26ac9e7f1ee9b118088c8` against the canonical RA-10 solution and all nine listed frozen sources/dependencies. Every recorded SHA-256 matches. The proposed theorem uses the actual `C=PAP`, with `P` selected from the supplied `QAhat`, an arbitrary ordered PSD witness `QC` for that same `C`, and the frozen Hermitian positive-part trace. It assumes only `k≤n` and `c>0`, so it includes empty, full-rank-projector, and singular-compression cases.

The equality is exact. Positive eigenvectors of `C` lie in `range(P)` because `C=PAP`; their spectral projector `E` is subordinate to `P`. On those `rank(C)` directions, `cP−C` has eigenvalues `c−h_i`. On the remaining `k−rank(C)` selected directions it has eigenvalue `c`; on `ker(P)` it has eigenvalue zero. The supplied `QC` may place its zero eigenvectors anywhere in the entire zero eigenspace, but orderedness and the audited zero tail ensure the first `k` list contains all positive `h_i` plus exactly the needed zero slots. Hence both sides equal `Σ_{h_i>0}max(c−h_i,0)+c(k−rank(C))`. This does not replace `P` by the identity or align zero eigenvectors of `QC` with `QAhat`.

The source's rotated `2×2` check is consistent: `A=diag(3,1)`, `P` onto `(1,1)/√2`, `C=2P`, `c=3` gives `cP−C=P`, so both traces are `1`. For `C=0`, both sides are `ck`; for `k=0`, both are zero, including `n=0`. The formula is the exact full-space representation of source `d=tr((cI_k−H)₊)`, with no loss of the selected zero eigenvalues.

After Lean implementation, independently audit the imported exact signature, source SHA-256, banned-token scan, LeanCert `kernel` trust/axioms, and aggregate import before using it in the later Lemma 2 bound.
