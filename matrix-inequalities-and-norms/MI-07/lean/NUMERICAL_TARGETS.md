# MI-07 numerical and semantic targets

**Statement-first review draft. No proof implementation has begun.** The exact definitions and seven Challenge exports must receive two independent statement approvals before a Proof or Solution is implemented. This document specifies the complete negative answer to the canonical constant-one triangle conjecture, using a rational member of the existing counterexample family. It does not claim the manuscript's stronger failure of every finite domination constant.

Formalization author: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. Mathematical counterexample and informal proof: **Matthew J. Colbrook**. No email address is included.

## Source and complete original target

The immutable source is upstream commit `e7252e5307781a7c897bca6cb124f6ab838f6809`:

- [Canonical MI-07 statement](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e7252e5307781a7c897bca6cb124f6ab838f6809/matrix-inequalities-and-norms/MI-07/README.md).
- [Complete Colbrook solution](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/e7252e5307781a7c897bca6cb124f6ab838f6809/matrix-inequalities-and-norms/MI-07/solution.tex), Theorem 1.1 and its full proof. The published proof treats every real parameter t>0. The specialization t=5/12 below is in that same family, although the source's optional fixed example uses t=1/2.

For every n≥1 and every pair of complex n×n matrices A,B, the canonical assertion asks whether there exist two arbitrary unitary matrices U,V such that

`M(A+B) ≤ U M(A) U* + V M(B) V*`,

where the comparison is ordinary positive-semidefinite order, and

`M(X) = lim_{m→∞, m∈positive integers} (|X|^m + |X*|^m)^(1/m)`.

The ordinary modulus is the positive square root `|X|=(X*X)^(1/2)`. The maximal symmetric modulus must be this genuine limit; it must not be an entrywise maximum, ordinary modulus, or alternative symmetric modulus. No self-adjointness, positivity, reality, commutation or rank assumption is placed on the arbitrary A,B in the full target. The witness is real but remains embedded in the complex field. All unitary choices, not only real orthogonal or diagonal choices, are excluded by the counterexample.

`TriangleConjecture` reproduces these quantifiers with `Fin n` matrices and `Matrix.unitaryGroup (Fin n) ℂ`. The final `not_triangleConjecture` export negates that entire predicate. It is not merely a scalar inequality or a statement about one prescribed pair of unitaries.

## Actual definitions and limit semantics

`matrixModulus X` is exactly Mathlib `CFC.abs X`. The generic `modulus_eq_sqrt` export must prove that it equals `CFC.sqrt (X.conjTranspose * X)` and is PSD. Both real powers and positive square roots therefore use continuous functional calculus for the actual matrix star algebra.

`rootSequence X r` is

```text
CFC.rpow (matrixModulus X ^ (r+1) + matrixModulus X.conjTranspose ^ (r+1))
         (((r+1 : ℕ) : ℝ)⁻¹).
```

The inner powers are actual natural powers in the matrix ring. The outer power is explicitly `CFC.rpow`; it is not the pointwise real-power instance inherited from functions. Index r starts at zero solely to enumerate the positive source exponents m=r+1. No root at exponent zero is used, and every reciprocal exponent is strictly positive.

`maximalModulus X` is `Filter.limUnder Filter.atTop (rootSequence X)`. This standard limit function is totalized if a sequence fails to converge. **No such default is used in the counterexample.** The generic `maximalModulus_eq_of_tendsto` theorem identifies this function with any proved limit, and `witness_root_limits` must prove convergence at each of A, B and A+B. Consequently every occurrence used to refute the universal target is the genuine canonical limit. No convergence hypothesis is added to `TriangleConjecture`, `counterexample` or `not_triangleConjecture`. A generic existence theorem for every complex matrix is unnecessary for this complete negative answer and is not advertised as part of this project.

The topology in `Filter.Tendsto` is the ordinary finite product topology of complex matrix entries. Mathlib's `Matrix.instL2OpMetricSpace` is constructed by replacing the induced operator-norm topology with that same topology via the matrix-to-Euclidean-linear-map homeomorphism. To check the norm interpretation explicitly, `spectralNorm` is defined under the local scope `Matrix.Norms.L2Operator`, and the generic `root_limit_iff_spectralNorm` export must prove equivalence with `spectralNorm(rootSequence X r - L) → 0`. Thus the limit is also convergence in the genuine Euclidean operator norm, and no default matrix norm is silently substituted.

`unitaryConjugate U H` is `(U : Matrix) * H * (U : Matrix).conjTranspose`. The subtype `Matrix.unitaryGroup` contains the true unitary identities. The `≤` in the conjecture comes from `MatrixOrder`, meaning `(right-left).PosSemidef`. That is ordinary PSD order; the word "spectral" in the source's interpretation of the limit does not change the order in the triangle inequality.

## Exact rational witness

Choose the source family at

`t=5/12`, `s=13/12`, `s²=1+t²=169/144`.

Then

```text
A = P = [[1,0], [0,0]],
B     = [[0,5/12], [0,0]],
X=A+B = [[1,5/12], [0,0]].
```

The normalized right polar direction is `v=(12/13,5/13)`. Its squared Euclidean norm is `(144+25)/169=1`. Its actual rank-one projection is

```text
Q = v v* = [[144/169,60/169], [60/169,25/169]],
R = P+Q  = [[313/169,60/169], [60/169,25/169]].
```

In the frozen definitions, Q is `directionProjector` and R is `spanningSum`. Prove `P²=P`, `Q²=Q`, P and Q PSD, and R positive definite. The exact first principal entry of R is 313/169 and its determinant is 25/169, both positive. As optional proof-only certificates, its eigenvalues are 25/13 and 1/13, with complementary orthogonal projections

```text
Eplus  = (1/26) [[25,5], [5,1]],
Eminus = (1/26) [[1,-5], [-5,25]],
Eplus+Eminus=I, Eplus*Eminus=0,
R = (25/13)Eplus + (1/13)Eminus.
```

These optional finite identities are independently reconstructed in the rational precheck. The implementation may instead use the standard finite-dimensional spectral theorem with positivity of R; no explicit sorted eigenvalue calculation is required or promised as a separate export.

## Genuine polar identities

Every one of the following identities must be derived from the actual matrix products and positive square roots; none is a hypothesis or an assumed certificate:

| Matrix | Right modulus | Left modulus, equivalently modulus of the adjoint |
| --- | --- | --- |
| A | P | P |
| B | t(I-P) | tP |
| X=A+B | sQ | sP |

For an exact square-root verification, the relevant Gram matrices are

```text
A* A = A A* = P,
B* B = diag(0,25/144),
B B* = diag(25/144,0),
X* X = [[1,5/12], [5/12,25/144]],
X X* = diag(169/144,0).
```

In particular `sQ=[[12/13,5/13],[5/13,25/156]]`. Its square equals X*X and it is PSD, so it is the actual positive square root. This avoids numerical square-root approximation while preserving the exact functional-calculus definition. The public `witness_moduli` export includes all six polar identities and the projection/positivity facts needed to justify the limit reduction.

## Actual root-sequence limits

For each positive integer m, the finite projection identities give the exact pre-root matrices

```text
|A|^m + |A*|^m = 2P,
|B|^m + |B*|^m = t^m I,
|X|^m + |X*|^m = s^m R.
```

The proposed analytic route must justify the actual CFC reductions

```text
(2P)^(1/m) = 2^(1/m) P,
(t^m I)^(1/m) = tI,
(s^m R)^(1/m) = s R^(1/m).
```

Because R is positive definite, its true spectral values are strictly positive. Scalar continuity of `λ^a` at a=0, followed by the actual finite-dimensional CFC formula, yields `R^(1/m) → I`. Likewise `2^(1/m) → 1`. This proves the three required `Tendsto` conclusions

```text
rootSequence A → P,
rootSequence B → (5/12) I,
rootSequence X → (13/12) I.
```

All reciprocal-exponent limits, positivity conditions and natural-power/CFC conversions must be proved. There must be no assumed convergence, assumed scalar asymptotic, assumed R spectrum, or replacement of the sequence by a surrogate merely having the desired limit. General spectral-theorem lemmas may avoid explicitly computing the optional Eplus/Eminus certificates.

Applying the proved limit-identification bridge gives the actual maximal moduli

`M(A)=P`, `M(B)=(5/12)I`, `M(A+B)=(13/12)I`.

## All-unitary obstruction and complete negation

For arbitrary U,V in the genuine two-dimensional unitary group, cyclicity of trace and the unitary identities imply

```text
trace(U M(A) U* + V M(B) V*) = trace(P) + trace((5/12)I) = 11/6,
trace(M(A+B)) = trace((13/12)I) = 13/6,
trace(U M(A) U* + V M(B) V* - M(A+B)) = -1/3.
```

Every PSD complex matrix has nonnegative real trace. Thus this exact negative trace rules out ordinary PSD domination for every U,V. There is no optimization over unitaries and no selection of a favorable real subclass. The final numerical LeanCert obligation is only a retained point certificate such as `0 < (1/3 : ℝ)`; that certificate must participate in the negative-trace contradiction after the exact identities have been proved.

The `counterexample` export must combine the actual maximal-modulus identities, the exact left trace, and the right trace/trace gap/failure of PSD comparison for every pair of complex unitaries. Finally, specialize the full universal `TriangleConjecture` at n=2 and these A,B to obtain `not_triangleConjecture`.

The trace shortcut works because t=5/12 gives `2s-(1+2t)=1/3>0`. It is a scope-preserving specialization of Colbrook's family and supplies a shorter obstruction for the original constant C=1. It does not claim the stronger no-finite-C theorem, which requires a varying parameter and is outside this formalization.

## Computation and trust plan

The independent Python/Fraction precheck reconstructs rational matrices, products, projection identities and the trace gap solely to validate this draft. Its outputs are not Lean hypotheses. Proof production must use exact matrix algebra and actual Mathlib CFC/spectral/limit theorems, followed by the one scalar LeanCert certificate in explicit kernel mode. No interval subdivision, numerical eigensolver, numerical square-root approximation, or search over unitary matrices is warranted.

The exact pins are Lean `leanprover/lean4:v4.33.1`, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Final theorem dependencies may contain only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, custom mathematical axiom or native execution trust is allowed. The seven intentional Challenge placeholders are a separate target and must never be imported by Solution.

## Statement-review gate

Two independent referees must read the full canonical README and Colbrook solution, inspect the elaborated Definitions and Challenge, independently reconstruct the witness values, and report approval or required changes with exact hashes. In particular they must check the actual positive square root, positive integer exponents, genuine spectral norm topology, all three proved limit obligations, ordinary PSD comparison, unrestricted complex unitaries, and complete original negation without added convergence assumptions. Only after both reports approve the frozen boundary may proof implementation begin.
