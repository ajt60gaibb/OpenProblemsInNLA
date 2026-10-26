# TR-26 read-only proof preflight

Author: OpenAI Codex AI agent `/root/proof_route`, 2026-10-26. This is route research and author preflight, **not** an independent pre-proof approval, a Lean proof, or implementation authorization. No TR-26 proof declaration, canonical source, Target, README, ID registry, or index was edited. The only new Lean input contains `#check` API inspections, with no TR-26 theorem declarations.

## Result and exact input boundary

The proposed route is mathematically faithful, and the coordinator's three draft endpoint signatures are exactly the two conjuncts of the existing Target plus its literal full statement. I found no statement defect requiring a Target change. There is a manageable elementary algebra front end, but the complete proof is not a short lift of existing Mathlib discriminant machinery: full-ideal conormal control and fixed-degree binary discriminant multiplicities remain substantial new obligations.

`PREFLIGHT_INPUTS.json` records 24 original input hashes. Every byte matches the immutable source checkpoint `353ebcfcbbcfc08184c32f391ecb6068c7d9098f`, published base `5487945e5a72abd952b0c89915915de8cc9b3e65`, and the retained frozen copy. The canonical README and `ORIGINAL.md` match exactly. The registry retains all 217 ID/path entries. There is currently no canonical `tensor-computations/TR-26/lean/` package; the local scaffold consists of the concrete shared/frozen statement files and their existing specification reviews.

Principal bindings:

| Input | SHA-256 |
| --- | --- |
| Complete canonical README | `56f792c83ff7328f014eee02f89314b32ac6558adfae53753b4bfb87a15d9659` |
| Complete Colbrook manuscript, Markdown | `4a96398678689820dffd81522991fa4178062789afd657acc73194f0852185f8` |
| Manuscript TeX | `bfb2f0fce6d67649dc8faca5965f79f898c4cb040645e721df5095446cd89b8e` |
| Shared exact statement | `e0b38f44232ea35418e8afb9bcd0c1df0e2dd51642cda71e8bf62564a130095f` |
| Frozen Reviewed statement | `e1700dde28c3679f126eaae1ea7cb16e979a18e94f1e77d198996f0f6ede6820` |
| Exact numerical/algebraic specification | `630e5dfb41a844e1105fc9af698520458449e1b58336b23d182e16d292114624` |
| Coordinator draft CONTRACT | `26625969b0c33b85d5e6dcb59dd2c3c9f9ca1389fcc92f4b3f1f1facb81d56a0` |
| Coordinator draft Challenge | `122ad60aaddf59e91dacd627637cf7237b8614d83b6d2eead381a76a698d7aba` |

I read the complete credited Markdown manuscript, including all eight sections, both small-degree arguments, multiplicity proof, matrix-kernel discussion, scope and references; the original problem, shared/frozen definitions, specification and existing review records were compared directly. The original mathematical credit and source AI-assistance disclosures remain with Matthew J. Colbrook. This report does not claim new mathematical authorship or external human review.

## Fidelity assessment

The exact Target is, for every natural `d ≥ 2`,

```
HasReducedDegree d (6 * (d - 1)) (NonisotropicClosure d)
  ∧ HasReducedDegree d (2 * d) (IsotropicImage d).
```

`HasReducedDegree` demands a nonzero **squarefree homogeneous polynomial** in independent upper-triangle matrix coordinates with the exact projective zero set at every nonzero parameter. Nonzero homogeneity gives the actual total degree; there is no opaque degree predicate or multiplicity-counted eliminant. The Target does not require irreducibility of the nonisotropic equation, although the manuscript proves it.

The model preserves the unweighted Veronese embedding, all complex symmetric matrices, complex bilinear transpose without conjugation, both parameter directions and infinity. `VanishesOnOpen` ranges over every polynomial vanishing on the open critical correspondence. `Incidence` takes their common zeros at nonzero curve and matrix representatives; `JacobianSpace` spans the curve-variable partials of that entire ideal. Thus a proof about a convenient selected Wronskian equation alone will not satisfy `Ramification`. The isotropic set is the raw projected image; the other projected set has its separately specified Zariski closure.

The draft `nonisotropic_degree`, `isotropic_degree`, and `target` headers retain precisely these meanings, all `d ≥ 2`, and no extra assumptions. The draft CONTRACT correctly leaves the hard bridges as obligations rather than supplying them as premises. Final approval must bind the settled unified input lock and any concrete helper definitions; the earlier statement-only reviews and API checks are not that approval.

## Faithful decomposition

Put `m = 2d`, let the binary numerator be the actual quadratic form restricted to the curve, and let

```
D(a,b) = sum_(i=0..d) a^(2d-2i) b^(2i),
W_H(a,b) = (N_b D_a - N_a D_b)/(2d).
```

The binary Wronskian has fixed homogeneous degree `2m-2 = 4d-2`, even if a specialized affine polynomial loses leading coefficients. At `a=1` it equals `N'(t)D(t)-N(t)D'(t)`.

### 1. Concrete numerator, denominator and jets

A particularly simple right inverse for the numerator map uses a symmetric tridiagonal matrix. For prescribed coefficients `c_0,...,c_(2d)`, set `H_ii=c_(2i)` and `H_(i,i+1)=c_(2i+1)/2`, with other off-diagonal entries zero. Its actual quadratic numerator has exactly the prescribed coefficients. This avoids choosing arbitrary antidiagonal representatives while retaining the independent upper-triangle parameter space.

For the affine denominator, prove

```
(X²-1) * D(X) = X^(2d+2)-1.
```

Characteristic zero makes the right side separable, so `Separable.of_dvd` proves separability of D directly. Together with its monic degree `2d`, algebraic closedness gives exactly `2d` distinct complex roots. `D(0)=1` and its homogeneous value at infinity is one. Explicit roots-of-unity enumeration is unnecessary.

The only numerators with zero Wronskian are `N=cD`. This can also be proved without rational-function derivative infrastructure: `W=0` implies `D | D' N`; separability gives `IsCoprime D D'`, hence `D | N`. The bound `deg N ≤ deg D` and monicity make the quotient constant. Include `N=0` explicitly.

Use Taylor/Hasse coefficients and the Chinese remainder theorem for finite jets. Ordinary Lagrange interpolation provides values only; the file named `Polynomial/Hermite/Basic` concerns Hermite orthogonal polynomials, not jet interpolation. The higher-order jet surjectivity and its degree bound must be proved. Infinity can be handled by reversing coefficients and treating leading jets; a general projective-coordinate-change library is avoidable.

### 2. Full incidence and conormal bridge

The central geometric helper should establish, for **every** nonzero H, nonzero parameter pair `(a,b)`, nonzero scalar c and `z=c*veronese d a b`,

```
Incidence d z H ↔ W_H(a,b)=0,
Ramification d z H ↔
  W_H(a,b)=0 ∧ (∂a W_H)(a,b)=0 ∧ (∂b W_H)(a,b)=0.
```

These are proposed helper contracts, not established lemmas or new assumptions. Their definitions must be concrete and reviewed before implementation.

A direct two-chart coordinate-ring proof looks more focused than building general projective bundles. On `z_0 ≠ 0`, use `t=z_1/z_0` and normal equations `z_i z_0^(i-1)-z_1^i` for `i ≥ 2`; the reversed chart handles infinity. At each parameter point the functional `H ↦ W_H(a,b)` is nonzero, by numerator surjectivity and jets, including `D=0`. Localize where a coefficient of that functional is nonzero and solve for one matrix coordinate. This gives an actual polynomial graph with a prime local ideal. Prove that the full vanishing ideal localizes to these normal equations plus the Wronskian equation, then prove equality of their evaluated conormal spans. The normal gradients have rank `d-1`; the final gradient increases rank precisely when the tangent derivative is nonzero.

This is the principal incidence obligation. Nullstellensatz and partial-derivative APIs are available, but no ready theorem identifying this concrete full ideal/Jacobian was found. A proof must show why multiplying localized generators by units and changing generators preserves the evaluated derivative span. It must differentiate only in z, holding H fixed.

### 3. Isotropic equation and exact degree

For each distinct denominator root r, take the actual linear parameter polynomial `L_r(H)=N_H(1,r)`. At a simple root of D, `W(r)=-D'(r)N(r)`, and imposing `N(r)=0` also forces `W'(r)=0`. With the conormal bridge, this proves an exact raw-image equality with the union of `L_r=0`, including all kernel matrices.

Let `I_d = product_r L_r`. Surjectivity and value interpolation show these are nonzero, pairwise nonassociated linear forms. Each is irreducible over the field, and their product is squarefree, nonzero and homogeneous of degree `2d`. This is a tractable first complete conjunct once the full-ideal bridge is proved. It is not by itself a full Target proof.

### 4. Fixed-degree discriminant and reduced complementary factor

Construct the universal discriminant in the coefficients of a binary form of fixed degree `k=4d-2`, then substitute the actual Wronskian coefficient linear forms. Prove fixed-degree specialization, multiple **projective** root support, nonvanishing, and homogeneity of degree `2k-2=8d-6`.

One must then prove a genuine factorization

```
Delta_d = nonzero_constant * I_d * G_d,
```

with every factor multiplicity one, `G_d` squarefree, and `G_d` homogeneous of degree `6(d-1)`. The source's route proves the nonisotropic incidence image is a hypersurface, separates it from all isotropic hyperplanes, and establishes a generic pattern of one exactly double root. For `d ≥ 3`, use independent jets of total length four and six to exclude triple roots and two double roots. For `d=2`, retain the explicit numerator `N=t³`, denominator `1+t²+t⁴`, and `W=t²(3+t²-t⁴)`; its top coefficient excludes an infinity root.

The discriminant differential at a unique double root is a nonzero multiple of evaluation of the perturbation at that root. A purely algebraic proof using the resultant product formula and first-order nilpotent/Taylor calculations may avoid introducing analytic implicit-function infrastructure. That proof is still missing. Generic independence/dimension arguments also require actual formal arguments; the manuscript's concise projective-bundle sentences are not existing Mathlib results for this family. The Target permits a direct squarefree-factor proof instead of irreducibility, but taking a radical and merely retaining the original degree would be invalid.

### 5. Closure and matrix pullback

Prove exact zeros of `G_d` equal the original nonisotropic closure and exact zeros of `I_d` equal the original isotropic image. Work on affine cones with the actual surjective linear numerator map. A linear splitting identifies the matrix space with numerator coordinates times the kernel, so polynomial extension preserves irreducibility/squarefreeness and homogeneous degree, and closure commutes with this product.

The nonzero kernel has dimension `d(d-1)/2`, already one at `d=2`. A projective rational map `[H] -> [N_H]` alone omits its nonzero points. For these matrices the Wronskian is identically zero and all curve points ramify; both images contain them. Numerators proportional to D likewise give constant quotients and must stay in both loci. These are cone vertices, not extra components.

## Pinned API evidence and limits

`verification/proof-route-api/API_RESULT.json` records an actual exit-zero Lean 4.33.1 invocation checking **42 existing API names/types** against Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The complete output and source are retained. This is API inspection only. An initial unknown namespace for Lagrange's theorem was corrected to `Lagrange.eval_interpolate_at_node`; the failed inspection log is preserved separately. No TR-26 proof was attempted.

| Need | Existing checked APIs | Missing family-specific step |
| --- | --- | --- |
| Denominator and roots | `Polynomial.separable_X_pow_sub_C`, `Separable.of_dvd`, `nodup_roots`, `IsAlgClosed.card_roots_eq_natDegree` | Geometric-sum factorization and actual degree. |
| Numerator and linear pullback | `Matrix.toMvPolynomial`, `toMvPolynomial_isHomogeneous`, `LinearMap.toMvPolynomial_comp` | Tridiagonal right inverse and exact evaluation identity. |
| Jets | `Polynomial.taylor_coeff`, `taylor_coeff_one`, `taylorAlgHom`, `degreeLTEquiv`, `Ideal.pi_mkQ_surjective` | Uniform finite jet interpolation and degree control, including infinity. |
| Full ideal/conormal | `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`, `pderiv_mul`, `pderiv_pow`, `aeval_sumElim_pderiv_inl`, homogeneous Euler identity | The actual localized ideal and rank equivalence above. |
| Discriminant | `Polynomial.sylvester`, `resultant`, `resultant_map_map`, `resultant_deriv`, `resultant_eq_prod_roots_sub`, `discr` | Fixed-degree binary support/specialization, homogeneity, unique-double-root differential and squarefree family restriction. |
| Reduced degree and extension | `IsHomogeneous.prod`, `aeval`, `totalDegree`, `irreducible_of_totalDegree_eq_one`, `Finset.squarefree_prod_of_pairwise_isCoprime`, `prime_C_iff`, `prime_rename_iff`, `sumAlgEquiv`, `finSuccEquiv` | Matrix splitting, closure-product identity and exact pulled-back equations. |

Two API traps are material. Mathlib's `Polynomial.wronskian a b` is `a*b' - a'*b`, so the manuscript affine form is `wronskian D N`, not `wronskian N D`. Also `Polynomial.discr f` uses **f.natDegree**, and `resultant_eq_zero_iff` uses actual degrees. Neither alone gives the fixed-degree binary discriminant at leading-coefficient degeneracies. Losing this distinction would omit projective infinity or assign wrong discriminants to the zero form.

## Contract recommendation

Retain the coordinator's exact three endpoints without adding hypotheses. Freeze the final unified original-input lock and concrete binary/helper definitions, and obtain two independent non-author pre-proof approvals before any implementation. The recommended author partition is elementary binary/jet algebra; full-ideal incidence/conormal charts; and universal discriminant/reduced-factor plus final closure/pullback. The latter two must expose actual theorems, not assumed geometric certificates. The complete target remains the conjunction of the two all-dimension reduced-degree endpoints; a successful isotropic or coefficient calculation must stay labeled partial until the nonisotropic endpoint is proved and independently replayed.
