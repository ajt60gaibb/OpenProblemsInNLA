# MF-16 numerical statements before proof

**Phase: statement-only draft for two independent reviews.** No `Proof.lean` or `Solution.lean` implementation exists. The nine explicit contracts are in `Challenge.lean`. Any `#eval` result or Python result below is a diagnostic, not a proved theorem or substitute for the later kernel certificate.

Mathematical counterexample: **Matthew J. Colbrook**. Formalization: **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, with AI assistance. Original conjecture/source credit remains Hillar–Johnson and Armstrong–Hillar. No degree theorem is assumed.

## Complete target and actual semantics

`WordUniquenessConjecture` quantifies over **every finite list of exactly the two letter constructors `Letter.X` and `Letter.B`**, requires equality with its actual list reversal and an actual occurrence of `X`, then quantifies over **all complex Hermitian positive definite two-by-two B and P**. It asserts exactly one complex Hermitian positive definite X whose actual written-order list product equals P. `Matrix.PosDef` is the genuine Mathlib property with `ComplexOrder`; there is no real-only, diagonal, commuting, invertible-only or fixed-word restriction in this target. `evalWord` maps the letters to matrices and takes `List.prod`. The witness uses natural semiring powers only; no real powers, extra letters or modified word convention occur.

A single fixed word with two distinct admissible solutions refutes this full target. The formalization claims neither three solutions, a threshold for all exponents, a shortest counterexample, nor the separate general existence theorem.

## Unchanged exact source matrices and ordinary word

The witness word is `[X,B] ++ replicate 12 X ++ [B,X]`, containing **16 letters, 14 occurrences of X and 2 of B**. Its reversal agrees with itself. For every real or complex pair of matrices its actual evaluation must equal `X * B * X^12 * B * X`.

The unchanged real source matrices are

```math
B=\begin{pmatrix}1&4\\4&17\end{pmatrix},\quad
X_0=\begin{pmatrix}3&0\\0&1\end{pmatrix},\quad
P=\begin{pmatrix}4783113&6377496\\6377496&8503345\end{pmatrix}.
```

The target obligations prove, with actual matrix operations,

```math
\det B=1,\qquad \det X_0=3,\qquad
\det P=4782969=3^{14},\qquad X_0 B X_0^{12}B X_0=P.
```

Their entrywise real-to-complex images must all satisfy genuine complex `Matrix.PosDef`. The definition of those images is `Matrix.map Complex.ofReal`, not a separately stipulated positive matrix.

## Three polynomial equations and semantic bridges

Use three independent real coordinates v=(x,y,z) and the actual symmetric matrix

```math
S=\begin{pmatrix}x&y\\y&z\end{pmatrix},\qquad s=x+z,\quad t=s^2.
```

Define the following polynomials in Horner form:

```math
u(s)=s\bigl(t(t(t(t(t-30)+324)-1512)+2835)-1458\bigr),
```

```math
v(s)=3\bigl(t(t(t(t(t-27)+252)-945)+1215)-243\bigr).
```

The symbol v(s) in this display is the identity coefficient, distinct from the coordinate vector named `v` in Lean. `linearCoefficient` and `identityCoefficient` name these functions. When the **actual** determinant of S is 3, the `twelfth_power_reduction` contract proves

```math
S^{12}=u(\operatorname{tr}S)S-v(\operatorname{tr}S)I.
```

This is a theorem about actual matrix powers, not a definition of a recurrence or assumed characteristic-polynomial equation. It follows from genuine two-by-two Cayley–Hamilton/finite algebra during proof implementation.

Let a=x+4y, b=4x+17y, c=y+4z, d=4y+17z. The exact polynomial AST defines

```math
g_0=xz-y^2-3,
```

```math
g_1=u(s)(xa^2+2yab+zb^2)-v(s)(a^2+b^2)-4783113,
```

```math
g_2=u(s)(xac+y(ad+bc)+zbd)-v(s)(ac+bd)-6377496.
```

Only rational constants, variables, addition, multiplication and negation appear. There is no division expression, square root or unsupported AD primitive. In particular, the `(3+y²)/x` parameterization used by the manuscript is **not** an assumed substitute for the matrix or a denominator-changing expression in this system. The determinant is enforced as its own equation.

The unconditional `polynomial_word_equivalence` contract proves exactly

```math
\operatorname{SystemZero}(g,(x,y,z))\iff
\det S=3\ \land\ (SBS^{12}BS)_{11}=P_{11}\ \land\
(SBS^{12}BS)_{12}=P_{12}.
```

All Expr evaluation and polynomial/matrix bridges must be proved. The actual determinant equation supplies the Cayley–Hamilton premise; it is not an extra hypothesis restricting the conjecture.

## Exact single-box certificate

The adapted three-dimensional box is centered near the **second additional source root** (the one with x approximately 3.4943451066). Its rational center is

```math
m=\left(\frac{17471725533}{5000000000},
-\frac{51638297}{156250000},
\frac{2224465749}{2500000000}\right),\qquad
\rho=\frac1{10000000}.
```

The complete closed box is the Cartesian product of these intervals:

| Coordinate | Lower endpoint | Upper endpoint |
| --- | --- | --- |
| x | `17471725033/5000000000` | `17471726033/5000000000` |
| y | `-413106501/1250000000` | `-413106251/1250000000` |
| z | `2224465499/2500000000` | `2224465999/2500000000` |

The exact rational preconditioner is

```math
C=\begin{pmatrix}
17591641083/500000000 & 20183/10000000000 & -17029/10000000000\\
-11575092327/500000000 & -2477/2000000000 & 10667/10000000000\\
-21469001731/5000000000 & -2797/10000000000 & 2319/10000000000
\end{pmatrix}.
```

The explicit numerical contract is

1. `krawczykCheck polynomialSystem rootBox rootCertificate {} = true`;
2. `det C = 790668616748253/62500000000000000000000000000`;
3. the actual checker's `boxRadius rootBox rootCenter = 1/10000000`;
4. the actual interval-matrix bound of `I-CJ` over **the entire box** is `<27/1000`.

Every item is a proof obligation, with **kernel-only** certificate reduction. The pinned checker itself checks AD support, center containment, nonzero actual preconditioner determinant, strict infinity-norm contraction and strict self-map enclosure. Its actual `krawczykCheck_sound` theorem derives differentiability, correct interval Jacobian bounds, closedness/completeness/convexity of the box, a genuine contraction fixed point, and the fixed-point/zero equivalence. These are library theorems to be consumed, not new project assumptions. The `certified_root` contract requires the resulting **actual unique real system zero in that box**.

The exact exploratory Fraction arithmetic finds contraction approximately 0.0264384, center displacement less than 4×10^-11, and strict inclusion margin greater than half the radius. Full exact values and reproducible AST/interval arithmetic are retained in `reviews/statement-evidence/`. The displacement and half-radius estimates are supplementary diagnostics; the advertised Lean numerical export is the four-item contract above. A successful machine `#eval` is also only a diagnostic. The later proof must retain the exact checked Boolean proposition and prove it in the kernel.

There is one box and no subdivision, interval precision search or transcendental evaluation. Rational arithmetic is exact. The default evaluation configuration is explicit `{}`; its transcendental/Taylor parameters have no approximation role for this constant/add/multiply polynomial fragment. This avoids the manuscript's 110-decimal fixed-point arithmetic and radius10^-40 boxes without assuming their existence certificates.

## Recovering the complete complex solution and full negation

`root_to_matrix` requires that every actual zero in the box yields:

- x>3, hence positivity of the leading minor and separation from X0;
- genuine complex positive definiteness of `complexify (symmetricMatrix v)`;
- equality of **all four entries** of the actual complex word evaluation with P;
- a matrix unequal to X0.

The determinant equation and x>0 give real/complex positive definiteness through the actual quadratic form or an exact LDL congruence. Real multiplication/powers/list products must commute with the real-to-complex map. For the remaining word entry, its symmetry is proved, its actual determinant is `det(S)^14 det(B)^2=3^14`, and the two known entries with **P11>0** determine its second diagonal entry. No nonsingularity, missing entry or positive-definiteness bridge is assumed.

Together with the actual source solution X0, the `counterexample` export has two distinct complex Hermitian positive definite solutions. `not_wordUniquenessConjecture` then negates the **entire original all-word/all-complex-PD-pair assertion**, using no additional premise or degree theorem.

## Gates

Definitions, Challenge, this numerical plan, correspondence, exact data, configuration and dependency pins are frozen only after successful statement elaboration and actual API/diagnostic inspection. Two independent statement approvals are required before **any proof implementation**. Later proof completion must pass independent final mathematical referees, actual Linux Comparator/default-kernel/rejection-control auditing, and publication review. Current canonical status remains Solved; no Lean-verified claim is made here.
