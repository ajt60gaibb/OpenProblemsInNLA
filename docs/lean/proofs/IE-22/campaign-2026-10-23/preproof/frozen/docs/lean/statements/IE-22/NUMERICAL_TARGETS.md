# IE-22 exact mathematical and numerical specification

Author: OpenAI Codex AI agent `/root/infra_audit`, 2026-09-28. This is a preimplementation specification. Two independent approvals must precede implementation; this document provides no Lean proof.

Permanent ID `IE-22`; canonical path `linear-systems-and-elimination/IE-22/README.md`; campaign base `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. The complete canonical README, including its Solved status, attribution and historical audits, is preserved byte-for-byte in `ORIGINAL.md` (SHA-256 `273ce377e8de3f575be53104f156f0436ffb571a3a464bb5d5693c0aa510c344`). Existing per-problem Lean files and review records remain preserved.

## Exact target and finite-dimensional semantics

For every fixed real `0 < theta < 1`, the original target asserts that the proposed real constant `c_theta = sqrt(h_theta)` has the eventual uniform upper-bound property for `M_(m,n)(theta)`, and that no smaller real constant has that property. The two clauses must both be present in a closed `Target : Prop`. This is a deterministic supremum over **all** real unit-row matrices; no random ensemble, generic position, full rank or incoherence condition restricts the matrices.

For natural dimensions `m,n`, matrices have real entries and indices `Fin m` and `Fin n`. Set `k(theta,m) = Nat.floor (theta * (m : Real))`, with real multiplication followed by floor. For a vector `x : Fin n -> Real`, let `unit(x)` mean `sum_j x_j^2 = 1`. Define

```
rowValue(A,i,x) = sum_j A_ij * x_j,
rowEnergy(A,S,x) = sum_{i in S} rowValue(A,i,x)^2,
sSq(theta,A) = inf { rowEnergy(A,S,x) :
                       S : Finset(Fin m), card S = k(theta,m), unit(x) },
unitRows(A) iff forall i, sum_j A_ij^2 = 1,
M(theta,m,n) = sup { Real.sqrt ((n : Real)/(m : Real)) * Real.sqrt(sSq(theta,A)) :
                     A : Matrix (Fin m) (Fin n) Real, unitRows(A) }.
```

Use actual real `sInf` and `sSup` of these explicitly specified sets, or an independently reviewed definition with exactly the same meaning. In the positive-dimensional target domain, `0 <= k <= m`, a retained row set of that cardinality exists, and the Euclidean unit sphere is nonempty and compact. Nonnegative quadratic forms attain their minima there, and the finite minimum over row subsets is attained. Therefore `sSq` equals the original variational `s_theta(A)^2`. It is zero for rank-deficient submatrices and for `k=0`; do not replace it by the least positive singular value. Repeated rows, negative entries and arbitrary row correlations are included. The square roots are nonnegative real square roots, with their original placement: `sqrt(n/m)*sqrt(sSq)`.

The supremum defining `M` is over a nonempty bounded set when `m,n >= 1`: repeating the first coordinate unit vector provides a matrix, and Cauchy–Schwarz gives each squared row product at most one on a unit vector, hence `0 <= sSq <= k <= m`. Thus `0 <= M <= sqrt(n)` and the real `sSup` is the genuine finite supremum, not the default value of an unbounded or empty set. All norms used to justify this correspondence are Euclidean, not function-space supremum norms. No attainment of the matrix supremum needs to be assumed.

For every real `a > 0` satisfying

```
(ProbabilityTheory.gaussianReal 0 1) (Set.Icc (-a) a) = ENNReal.ofReal theta,
```

define

```
h(a) = (1 / Real.sqrt (2 * Real.pi)) *
       integral_{t from -a to a} t^2 * Real.exp (-(t^2)/2) dt,
c(a) = Real.sqrt (h(a)).
```

The Gaussian API arguments are mean zero and variance one. Positive `a` with this exact quantile equation exists uniquely for every `theta` in `(0,1)`. Quantifying over all such `a` therefore retains the original `a_theta`, without a numerical quantile approximation, unconstrained `h`, or new restriction on `theta`. Endpoints carry no Gaussian mass. The definitions of `sSq`, Gaussian quantile and `h` may be shared with IE-21 only after both targets' independent reviews cover the shared source. IE-22 itself has no matrix probability-law assumptions.

## Uniformity and optimality quantifier order

For real `theta,c`, the upper-bound predicate is exactly

```
Upper(theta,c) iff
  forall epsilon : Real, 0 < epsilon ->
    exists N R : Nat,
      forall n m : Nat, 0 < n -> 0 < m -> N <= n -> R*n <= m ->
        M(theta,m,n) <= c + epsilon.
```

Here natural multiplication `R*n <= m` is equivalent to the original real ratio condition `m/n >= R` because `n > 0`. Allowing natural thresholds includes zero and is equivalent to integer thresholds: negative thresholds can be increased to zero or one without affecting existence or eventuality. `N,R` may depend on `theta,c,epsilon`, but must be chosen **before** `n,m`, and do not depend on a matrix. In the target `c=c(a)`, so the thresholds may also depend on the uniquely determined quantile. Both dimensions range over every positive natural satisfying the thresholds, including `m<n` whenever those thresholds admit it; no additional aspect-ratio condition may be silently added.

The no-smaller clause is

```
forall c' : Real, c' < c(a) -> not Upper(theta,c').
```

Equivalently, for each smaller `c'` there is some real `epsilon>0` such that for every pair of natural thresholds `N,R`, some positive `n,m` with `N<=n` and `R*n<=m` satisfies `c'+epsilon < M(theta,m,n)`. The tolerance in this negated property may depend on `c'`; requiring the violation at every tolerance would be stronger and incorrect. Negative candidate constants are included. Merely asserting the upper bound, a single sequence attaining it, or a lower bound for one matrix size does not supply this exact optimality clause.

The full target quantifies `forall theta a : Real`, assumes `0 < theta < 1`, `a > 0` and the Gaussian quantile equation, and concludes

```
Upper(theta,c(a)) and (forall c' : Real, c' < c(a) -> not Upper(theta,c')).
```

The canonical request fixes no numerical tolerance, finite dimension, convergence rate, algorithm or complexity bound. No interval computation or matrix sampling is needed to state it.

## Existing statement gap and scope discipline

The retained old `lean/Challenge.lean` conjoins upper bound and optimality with a `SupremumConverges` extension. In `lean/Definitions.lean`, that extension quantifies sequences with `m_j/n_j -> infinity` but **omits** `n_j -> infinity`, contrary to the original problem and the manuscript. For example, when `n_j=1`, every unit row is `+1` or `-1`, `sSq=floor(theta*m_j)`, and `M(theta,m_j,1)=sqrt(floor(theta*m_j)/m_j) -> sqrt(theta)`, not `sqrt(h_theta)`. Since `a_theta>0`, the Gaussian identity `h_theta=theta-2*a_theta*phi(a_theta)` gives `h_theta<theta`. The old extension therefore cannot be reused as the new target.

The new `Target` contains precisely the two canonical clauses above. The manuscript proves stronger results: an upper bound uniform in every `m>=1` for large `n`, an explicit squared normalized error `O_theta(n^(-1/6))`, and convergence of the supremum along sequences satisfying **both** original growth conditions. These results retain their mathematical credit and can support a future proof, but are not silently substituted for the exact original statement. Existing zero-vector and empty-energy supporting lemmas remain preserved and do not establish the full target. The old artificial matrix measurable-space instance is unnecessary for this deterministic problem and is not imported.

## Source credit and formal verification boundary

The retained mathematical resolution is by Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Its Theorem 2 and Sections 6–7 are in `references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.tex` (raw-byte SHA-256 `31a1949c07f63408538f04e3803d90e8d3d0c3d1e47dc89a2ffa5a04ef4f3880`); the independent agent review is `references/colbrook-recovered-2026-09-11/verification/reviews/IE-21-22-review.md` (SHA-256 `d174419a6f71de369b7608a53b36dffa9cd815e3fd65a70d16457318cb68234d`). Source disclosures of substantial AI assistance and the absence of external human peer review or formal proof certification remain intact. This specification does not claim new mathematical authorship or a proof.

Implementation must define a closed `Target : Prop` with actual real matrices, finite sums, infima, suprema, square roots and Gaussian integral semantics, with no target axiom, assumed uniform bound, uninterpreted extremizer or `sorry`. The final independent review must inspect all imported meanings and verify the two complete quantifier clauses, floor and degenerate retained sets, positive-dimensional supremum domain, Gaussian normalization and exact norm. Shared pins are Lean `4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. `#assert_statement` and `#assert_trust kernel` check the declared boundary; the frozen Comparator identity does not prove the problem. LeanCert's shared kernel smoke test is not a proof of the optimal constant.
