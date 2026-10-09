# IE-21 exact mathematical and numerical specification

Author: OpenAI Codex AI agent `/root/infra_audit`, 2026-09-28. This is a preimplementation specification. Two independent approvals must precede implementation; this document provides no Lean proof.

Permanent ID `IE-21`; canonical path `linear-systems-and-elimination/IE-21/README.md`; campaign base `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. The complete canonical README, including its Solved status, attribution and historical audits, is preserved byte-for-byte in `ORIGINAL.md` (SHA-256 `71783a338942837a9c37bf2d50801484e711e55ee36a8da62d009bad518ae3ba`). Existing per-problem Lean files and review records remain preserved.

## Exact original proposition and separately supplied quantitative answer

The independently exported `OriginalLimitTarget : Prop` states exactly the displayed canonical conjecture: for each fixed real `0 < theta < 1`, every sequence of positive natural matrix dimensions `(m_j,n_j)` with both `n_j -> infinity` and `m_j/n_j -> infinity`, and independent uniform unit-sphere rows, the ratio `s_theta(A_j)^2 / ||A_j||_2^2` converges in probability to the Gaussian trimmed second moment `h_theta`.

The source also asks for quantitative error bounds without prescribing their formula. The separately exported `QuantitativeAnswerTarget : Prop` will state the concrete finite-dimensional bound supplied in Sections 4–5 of Matthew J. Colbrook's retained manuscript, using the exact constants below. This is a credited answer to that unprescribed quantitative request, and a stronger specialization than the original displayed limit; it is **not** an equivalent original numerical conjecture. The campaign's combined `Target : Prop` is `OriginalLimitTarget and QuantitativeAnswerTarget`, so both boundaries are checked while the original proposition remains independently available unchanged.

## Concrete finite-dimensional definitions

For natural `m,n`, let matrices have entries in the real numbers and indices `Fin m` and `Fin n`. Define `k(theta,m) = Nat.floor (theta * (m : Real))`, with floor taken **after** real multiplication. Define

```
rowValue(A,i,x) = sum_j A_ij * x_j,
rowEnergy(A,S,x) = sum_{i in S} rowValue(A,i,x)^2,
unit(x) iff sum_j x_j^2 = 1,
sSq(theta,A) = inf { rowEnergy(A,S,x) :
                       S : Finset(Fin m), card S = k(theta,m), unit(x) },
opSq(A) = sup { sum_i rowValue(A,i,x)^2 : unit(x) }.
```

Use actual real `sInf` and `sSup` of these explicitly defined sets, or an independently reviewed definition with exactly the same meaning. For `n >= 1` and `0 < theta < 1`, the infimum set is nonempty and nonnegative: the unit sphere is nonempty, `0 <= k <= m`, and finite row subsets of that size exist. Each quadratic form is continuous on the compact Euclidean unit sphere, so this infimum is the attained minimum in the original definition. It equals `s_theta(A)^2`, including rank-deficient maps and the empty retained set `k=0`, where it is zero. Do not substitute a minimum over only the nonzero singular values. The supremum set is nonempty and bounded, and its value is the square of the induced **Euclidean** spectral norm. The unbundled function-space supremum norm is not the vector norm here. For unit rows and `m >= 1`, `opSq(A) > 0`, so the ratio is an ordinary nonzero-denominator ratio, not an artifact of totalized division.

For each dimension, use the actual real Euclidean space `E_n = EuclideanSpace Real (Fin n)` with its Borel measurable space and usual Lebesgue/Haar `volume`. Let `Sphere_n = Metric.sphere (0 : E_n) 1`, with its subtype measurable space. Define

```
nu_n = (volume : Measure E_n).toSphere,
sigma_n = (nu_n Set.univ)^(-1) • nu_n,
Omega_mn = Fin m -> Sphere_n,
mu_mn = Measure.pi (fun _ : Fin m => sigma_n).
```

Here inverse and measure scalar multiplication use nonnegative extended reals. For `n >= 1`, `nu_n` has finite positive total mass. Normalization is therefore a genuine probability measure. On Euclidean space, `Measure.toSphere` is the surface/cone measure characterized for measurable sphere sets `B` by `nu_n(B) = n * volume({r u : 0 < r < 1, u in B})`. After normalization it is the uniform rotation-invariant surface probability, including equal masses on the two points when `n=1`. Requiring only that rows lie on the sphere does not impose this law.

A sample `omega : Omega_mn` determines the matrix with row `i` equal to `(omega i).val`, using the underlying `Fin n -> Real` coordinates of `EuclideanSpace` (the `WithLp.ofLp` map). The **joint finite product measure** `mu_mn` fixes both identical uniform marginals and independence; no arbitrary law record or uninterpreted uniformity predicate is permitted. Probability may be expressed directly as this measure of a set in `ENNReal`. The pinned `Mathlib.MeasureTheory.Constructions.HaarToSphere` definitions, its finite/nonzero mass results, and `Mathlib.MeasureTheory.Constructions.Pi` product-law meaning must be inspected in final review. No artificial `MeasurableSpace := top` may be installed.

For a real `a > 0`, the quantile condition is

```
(ProbabilityTheory.gaussianReal 0 1) (Set.Icc (-a) a) = ENNReal.ofReal theta.
```

The Gaussian API takes mean and **variance**, so these arguments are the standard normal law. Define

```
h(a) = (1 / Real.sqrt (2 * Real.pi)) *
       integral_{t from -a to a} t^2 * Real.exp (-(t^2)/2) dt.
```

Quantify over every positive `a` satisfying that exact quantile equation; its unique existence for `theta` in `(0,1)` is the standard normal quantile fact, not an extra restriction on `theta`. Endpoints of the integration interval have measure zero; using `Icc` for quantile and an interval integral for `h` preserves the source exactly. Do not replace `a` or `h` by approximations, a fixed rational threshold or an unconstrained constant.

## OriginalLimitTarget quantifiers

Quantify in this order: all real `theta,a`; hypotheses `0 < theta < 1`, `a > 0` and the Gaussian quantile equality; all functions `m,n : Nat -> Nat`; positivity of `m_j,n_j` for every `j`; the two limits

```
Tendsto (fun j => (n j : Real)) atTop atTop,
Tendsto (fun j => (m j : Real) / (n j : Real)) atTop atTop.
```

Conclude that for every real `epsilon > 0`,

```
Tendsto
  (fun j => mu_(m_j,n_j) {omega |
     epsilon <= abs (sSq(theta,A(omega)) / opSq(A(omega)) - h(a))})
  atTop (nhds (0 : ENNReal)).
```

This is convergence in probability on the varying sample spaces; no cross-`j` coupling is requested. On probability measures this extended-real expression is equivalent to the usual real-valued probability limit. Positivity records the physical matrix dimensions. Any original sequence permitting finitely many exceptional zero dimensions has an eventually positive tail because of the two growth conditions; removing that finite prefix does not change either limit. No growth rate beyond the two displayed limits is imposed. There is no assumed spectral conditioning, no lower bound on `floor(theta*m)` and no dimension-dependent retention fraction.

## QuantitativeAnswerTarget constants, domains and event

For all real `theta,a` satisfying the same conditions, all naturals `m >= 1,n >= 2`, and all real parameters

```
0 < t < 1,       0 < delta < 1,       0 < eta <= (1-theta)/2,
```

set the following exact real quantities:

```
L = 2 / (1-theta),
D = 2*L*eta + L/(m : Real) + 2*(1+t)*delta,
E = D + Real.sqrt (2/(n : Real)),
F = (E+t)/(1-t),
B = 2*(9 : Real)^n * Real.exp (-(m : Real)*t^2/512)
    + 5*(1+2/delta)^n * Real.exp (-2*(m : Real)*eta^2).
```

The event whose probability is bounded is the **union** of the two failures,

```
Bad = {omega |
  E < abs (((n : Real)/(m : Real))*sSq(theta,A(omega)) - h(a))
  or F < abs (sSq(theta,A(omega))/opSq(A(omega)) - h(a)) }.
```

The target inequality is `mu_mn Bad <= ENNReal.ofReal B`. Thus outside one common event of probability at most `B`, both manuscript errors hold simultaneously. This is the common covariance/net event used in Sections 4–5, not two independently asserted events whose union bound would acquire an extra factor. Retain the exact constants `2,9,512,5,2`, the exponent `n`, the finite-sample floor term `L/m`, and the denominator `1-t`. The bound need not be below one for every parameter choice; that is a legitimate, possibly uninformative probability bound. The manuscript's finite-dimensional concentration argument uses `n >= 2`, but the original asymptotic target includes every positive initial dimension. Do not silently replace the `or` in `Bad` by `and`, strict error exceedance by a smaller event, or either error by a bound for a fixed direction.

## Why the quantitative specialization adds no growth assumption

This correspondence calculation checks the logical scope of the statement; it is not a formal Lean proof of the manuscript's probability inequality. Write `Q_j=m_j/n_j`. For any two original growth conditions, eventually `Q_j>1` and choose `u_j=32*sqrt(log(Q_j)/Q_j)`, then `t=eta=delta=u_j`. Since `log Q/Q -> 0`, all parameter restrictions eventually hold for each fixed `theta`. Also `n_j -> infinity` and `m_j -> infinity`, so `E_j -> 0` and `F_j -> 0`.

For these choices the first failure term is exactly `2*(9/Q_j^2)^(n_j)`. For `Q_j >= exp(1)`, `1+2/u_j <= 2*sqrt(Q_j)`, so the second is at most `5*(2*Q_j^(-2047.5))^(n_j)`. Each base tends to zero; eventual `n_j >= 1` suffices for both powers to vanish. Therefore `B_j -> 0` without any comparison between how quickly `Q_j` and `n_j` diverge. For each fixed `epsilon>0`, eventually `F_j<epsilon`, so the original event `epsilon <= abs(ratio-h)` is contained in the ratio part of `Bad`. The proposed quantitative answer therefore entails the original probability limit with exactly its existing growth hypotheses. No logarithmic lower bound on `m/n` as a function of `n` is introduced.

## Source credit, old scope gaps, and verification boundary

The retained mathematical resolution is by Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. The quantitative answer above is transcribed from `references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.tex`, Sections 4–5 (raw-byte SHA-256 `31a1949c07f63408538f04e3803d90e8d3d0c3d1e47dc89a2ffa5a04ef4f3880`). The source discloses substantial AI assistance. Its subsequent independent agent review is retained at `references/colbrook-recovered-2026-09-11/verification/reviews/IE-21-22-review.md` (SHA-256 `d174419a6f71de369b7608a53b36dffa9cd815e3fd65a70d16457318cb68234d`). Existing source credit, mathematical Solved status, and limitations remain unchanged; this campaign claims neither a new proof nor human peer review.

The older `lean/Definitions.lean` calls its support-plus-independence record `SphericalRowLaw`, but its `row_uniform_on_sphere` field only demands unit norm almost surely. Deterministic equal rows satisfy that condition and independence, yet need not have the proposed limit. Its matrix measurable space is artificially set to `top`. These are substantive statement gaps, so no old challenge axiom or probability record is imported into the new target. Existing zero-vector and empty-row-energy lemmas remain credited supporting work, not proofs of the full result.

Implementation must use closed `Prop` definitions with concrete matrix, measure, integral and limit semantics. Both named components and the combined target require `#assert_statement` and `#assert_trust kernel` checks, plus independent review of the final imported meanings and frozen boundary. Shared pins are Lean `4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. Comparator checks identity with a separately frozen statement; they do not prove either proposition. No interval quadrature, random samples or finite-dimensional truncation is needed to state these universal claims. LeanCert's kernel smoke test does not certify this problem's truth.
