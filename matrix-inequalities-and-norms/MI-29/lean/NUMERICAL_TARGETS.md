# MI-29 statement boundary and numerical obligations

Status: statements compiled; proof implementation must wait for two independent statement approvals.

This project formalizes Matthew J. Colbrook's negative resolution of MI-29. George Stepaniants is the formalization author, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. Colbrook retains attribution for the mathematical counterexample, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. No email address, first-discovery claim, external human review, or completed formal certification is claimed here.

## Complete canonical target and source mapping

The canonical source is `matrix-inequalities-and-norms/MI-29/README.md` at upstream revision `e7252e5307781a7c897bca6cb124f6ab838f6809`. The complete standalone informal proof `matrix-inequalities-and-norms/MI-29/solution.tex` and its companion `solution.md` were read before drafting these statements. The mathematical argument is Theorem 1.1 and its proof, including its hypothesis-distinction remark.

The full canonical conjecture is:

For every integer `n ≥ 1`, every positive definite `A ∈ ℂ^(n×n)`, every invertible Hermitian `B ∈ ℂ^(n×n)`, and every pair of real parameters `k,p ≥ 0`,

`det(A^k + |AB|^p) ≥ det(A^k + |BA|^p)`.

Here `|X| = (XᴴX)^(1/2)` is the positive matrix modulus, and powers of positive matrices are defined by spectral functional calculus. Zeroth powers are the identity matrix. Both determinants are positive real numbers. No commutation between `A` and `B`, and no positivity of `B`, is assumed.

The canonical README notes that an earlier source also states a semidefinite variant. This formalization preserves the canonical positive-definite/invertible formulation exactly; it does not add a separate theorem about singular inputs. The known `k=2` theorem and the variant requiring `B>0` are outside the negative claim. A counterexample with `k=6`, `p=8`, and indefinite `B` refutes the full all-parameter canonical assertion without contradicting either of those restricted statements.

## Exact formal meanings

`NLA/MI29/Definitions.lean` imports only pinned mathlib modules and contains no local theorem, custom axiom, placeholder, or solution import. Its order scopes are explicitly `ComplexOrder` and `MatrixOrder`.

| Definition or predicate | Mathematical meaning |
| --- | --- |
| `Matrix (Fin n) (Fin n) ℂ` | A square complex matrix of the original order, with labeled finite coordinates. |
| `A.PosDef` | Mathlib's genuine complex positive definiteness, including Hermitian symmetry and strictly positive quadratic forms. |
| `B.IsHermitian` | Equality to its conjugate transpose. This permits an indefinite matrix. |
| `IsUnit B` | Invertibility in the square matrix ring; no candidate inverse or spectral list is supplied as an assumption. |
| `spectralPower A r` | The explicit function `CFC.rpow A r`, based on unital continuous functional calculus of the nonnegative real spectrum. |
| `matrixModulus X` | The actual `CFC.abs X`, defined in mathlib as `CFC.sqrt (star X * X)`, where matrix star is conjugate transpose. |
| `leftMatrix A B k p` | `spectralPower A k + spectralPower (matrixModulus (A*B)) p`. |
| `rightMatrix A B k p` | `spectralPower A k + spectralPower (matrixModulus (B*A)) p`. |
| `leftDet`, `rightDet` | The actual complex matrix determinants of those two matrices. |
| `ModulusDeterminantConjecture` | The full universal assertion over positive dimensions, complex inputs, positive-definite/invertible-Hermitian hypotheses, and all nonnegative real exponents. |

There are two critical instance choices. First, a matrix is represented by a function type, so writing a real power through an unintended pointwise `Pow` instance would change the problem. `spectralPower` calls `CFC.rpow` explicitly instead. Natural powers such as `A^(6 : ℕ)` are ordinary matrix-ring powers and appear only in the required proved reductions. Second, `MatrixOrder` selects the positive-semidefinite matrix order, not coordinatewise complex inequalities. The scoped complex scalar order expresses equality of imaginary parts together with comparison of real parts. The required generic `comparison_positive_real` theorem establishes that both determinant imaginary parts actually vanish and both real parts are strictly positive; the main comparison therefore has precisely its ordinary real meaning.

The unital `CFC.rpow` is essential at exponent zero. Mathlib also has a nonunital nonnegative-power operation whose zeroth-power behavior differs; that operation is not used for `spectralPower`. The square root used by `CFC.abs` is the genuine nonnegative CFC square root of `XᴴX`. Every such Gram matrix is positive semidefinite, so no arbitrary fallback on a nonpositive input is being substituted for a modulus. Under the canonical hypotheses the matrices to which arbitrary spectral powers are applied are positive definite, and all displayed powers have their intended spectral meaning.

The relevant pinned mathlib definitions and APIs were inspected directly:

- `Mathlib/Analysis/Matrix/Order.lean`: matrix order, its relation to `PosSemidef`, and the relation between `IsStrictlyPositive` and `PosDef`.
- `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean`: explicit `CFC.rpow`, `rpow_zero`, `rpow_natCast`, `sqrt_eq_rpow`, `sq_sqrt`, and strict positivity of spectral powers.
- `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Abs.lean`: explicit `CFC.abs`, its nonnegativity, and `CFC.abs_sq`.
- `Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean`: actual matrix continuous functional calculus, rather than a formal symbol for spectral powers.

## Required analytic bridges

The first public export must prove, for every square complex positive semidefinite matrix `A` and natural number `r`,

`spectralPower A (r : ℝ) = A^r`.

The case `r=0` establishes the canonical identity-matrix convention. This statement does not restrict the real exponent variables in the conjecture to integers; it only provides the justified reduction used at the explicit integer witness.

The second public export must prove, for every square complex matrix `X`, all three assertions:

1. `matrixModulus X = CFC.sqrt (Xᴴ * X)`;
2. `(matrixModulus X).PosSemidef`;
3. `spectralPower (matrixModulus X) 8 = (Xᴴ * X)^4`.

These assertions must follow from actual mathlib CFC definitions and theorems. The desired proof uses natural-power agreement and the square-root identity `|X|²=XᴴX`, then associates the natural powers as `|X|⁸=(|X|²)⁴`. No approximate matrix square root, supplied spectral decomposition, analytic bridge assumption, or custom axiom is allowed.

The third public export, `comparison_positive_real`, must prove under the complete canonical hypotheses that `leftDet` and `rightDet` have zero imaginary part and strictly positive real part. This connects the scoped complex comparison to the positive real determinant comparison stated by the problem. These are conclusions to prove, not extra premises imposed on the original target.

## Exact witness and numerical obligations

Set `n=3`, `k=6`, `p=8`, and define the following matrices over `ℂ`, with zero imaginary parts:

```
A = diag(2, 1, 1/2),
M = [[-1, 2, 0],
     [ 2, 1, 2],
     [ 0, 2, 1]],
B = (1/5) M.
```

The witness export must prove `A.PosDef`, `B.IsHermitian`, and `IsUnit B`, with the exact determinant identity `det B = -1/125`. It must also prove `¬B.PosSemidef` and `¬(-B).PosSemidef`, documenting that the permitted Hermitian factor is genuinely indefinite. The diagonal entries `B₀₀=-1/5` and `B₁₁=1/5` provide exact witnesses for the two failures of semidefiniteness. Positivity and all matrix conditions are proof obligations, never user-supplied certificates.

The spectral powers used by the actual witness determinants must be related to algebraic matrix powers in Lean:

- `spectralPower A 6 = A^6`;
- `spectralPower (matrixModulus (A*B)) 8 = (B*A²*B)^4`;
- `spectralPower (matrixModulus (B*A)) 8 = (A*B²*A)^4`.

The second and third identities use the Hermitian equalities of the actual `A,B`, together with the generic modulus bridge. The positions of `A` and `B` must remain exactly as shown. The moduli have the same singular spectrum, but they need not have the same alignment relative to `A`; exchanging these two products would erase the content of the counterexample.

After those proved analytic reductions, the exact determinant obligations are:

| Quantity | Required exact value |
| --- | --- |
| `leftDet A B 6 8` | `136990346414301954149 / 61035156250000000000` |
| `rightDet A B 6 8` | `4537743716162890657 / 1907348632812500000` |
| `rightDet A B 6 8 - leftDet A B 6 8` | `21036678407451 / 156250000000000` |

These identities are equalities in `ℂ` to rational constants with zero imaginary parts. The final witness must prove the strict complex-order reversal `leftDet A B 6 8 < rightDet A B 6 8`, which becomes the strict reverse real inequality using the exact determinant identities or the generic reality bridge.

A separate precheck in `reviews/numerical-statement-precheck.json` independently computes these constants using Python `Fraction` arithmetic, explicit matrix multiplication, natural powers, and the six-term determinant formula. It also checks the source's optional two-coefficient identity: with `D=A^6`, `H=(M*A²*M)^4`, and `J=(A*M²*A)^4`,

`det(D+zJ)-det(D+zH) = (2089017/16) z - (31188746592549/1024) z²`.

The cubic and constant coefficients cancel, and `z=5^-8` gives the displayed gap. This polynomial identity is a possible proof implementation aid, not a replacement for the selected exports or a new assumed premise. Only the exact point values and actual matrix/CFC connections are mandatory formalization targets. The numerical precheck is not a Lean certificate and does not establish those analytic connections.

## Public exports and proof gate

The five declarations in `Challenge.lean` are the reviewed statement boundary:

1. `NLA.MI29.spectralPower_natCast`;
2. `NLA.MI29.modulus_power_eight`;
3. `NLA.MI29.comparison_positive_real`;
4. `NLA.MI29.counterexample`;
5. `NLA.MI29.not_modulusDeterminantConjecture`.

The last export negates `ModulusDeterminantConjecture` itself, rather than a fixed-dimension or integer-exponent substitute. Its proof must instantiate all original quantifiers with the actual witness, prove `1≤3`, `0≤6`, and `0≤8`, and use the strict reverse determinant inequality to contradict the proposed comparison.

The Challenge placeholders are intentional for separate-environment comparison. **No proof implementation may begin until two independent statement referees approve the compiled definitions, Challenge, and these numerical obligations with their recorded hashes.** Any later change to a mathematical statement or definition requires renewed review. The final `Solution.lean` must reproduce the selected declarations from completed proof modules and must never import `Challenge.lean`.

## Computation and trust plan

The project follows the statement/Challenge/Solution separation studied in the Forsythe example. All nonnumerical work is assigned to existing mathematical CFC and matrix APIs with proved reductions. Exact finite matrix arithmetic then evaluates just two `3×3` determinants. Reuse intermediate Gram matrices and fourth powers. The polynomial gap identity is available if it reduces expansion work; there is no need to verify it redundantly if direct exact determinant certificates are smaller.

LeanCert will be used in explicit kernel mode only for the rational point certificate

`0 < (21036678407451 : ℝ) / 156250000000000`.

There are no intervals to subdivide, parameter grids, numerical eigenvalue calculations, or approximate square roots. The chosen numerical point is separated from zero, and all denominators are exact positive integers. The analytic and matrix certificates must establish that this scalar gap is the actual right-minus-left difference in the original claim.

The project uses Lean `4.33.1`, LeanCert commit `621a43d7cf21f87872392a01e874f2f1dbddc926`, and mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Matching dependency sources and compiled artifacts were APFS clone-copied into the isolated worktree; the original cache was not changed. Both pinned dependency source trees were checked clean.

Completed exports and the LeanCert certificate must pass `#assert_trust kernel` and axiom inspection, with only `propext`, `Classical.choice`, and `Quot.sound` permitted. No proof placeholder, custom axiom, native execution trust, or `native_decide` may enter their closure. Independent final proof referees, Linux Comparator, `formalization.yaml`, and reproducibility evidence remain separate required gates. A statement-only build is not a completed formal verification claim.
