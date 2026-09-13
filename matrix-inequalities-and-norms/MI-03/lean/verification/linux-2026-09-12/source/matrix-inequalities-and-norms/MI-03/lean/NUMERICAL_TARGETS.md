# MI-03 exact mathematical and numerical boundary

**Statements only, 12 September 2026. No implementation exists.** Two independent written statement approvals are required before proof work. Eight isolated Challenge placeholders declare obligations without proving them. Canonical status remains Solved on the basis of the retained informal proof; no Lean promotion is made.

Formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI assistance. Mathematical proof: Matthew J. Colbrook. The source is the complete MI-03 Theorem 1.1 and its proof at repository revision `c0601d8825e9f9e744212c62e6a43fefc1c60a22`.

## Original target and the infimum

For each natural k, an admissible constant c is a **nonnegative real number** such that the original matrix-order inequality holds for every positive dimension n and every tuple of k complex square matrices whose genuine induced Euclidean operator norms are at most one. Define

```math
G(A,c)=cI+\sum_j |A_j|-\left|\sum_j A_j\right|.
```

The requirement is actual positive semidefiniteness of G. Here |X| is the genuine principal positive square root of X*X, implemented by `CFC.sqrt`. Ordinary matrix multiplication, complex conjugate transpose, actual PSD order and the norm of `Matrix.toEuclideanCLM` are used throughout.

`sharpConstant k` is the actual real infimum of the complete admissible set. The final original target quantifies every odd k≥3 and asserts `sharpConstant k=k/4`. The proposed stronger supporting theorem for all k≥2 establishes **IsLeast** of that genuine set and its infimum equality. This must prove the set is nonempty and bounded below as needed; an empty-set convention or an assumed infimum cannot establish the target. There is no fixed-dimension, Hermitian, invertibility or generic-position restriction on the universal upper bound.

## Exact upper-bound obligations

For arbitrary complex X in every positive dimension, first prove that R=|X| is PSD, R²=X*X and its genuine operator norm equals ||X||. If ||X||≤1, prove that I−R and R−R² are both PSD. These functional-calculus/order/norm bridges are theorem conclusions, not supplied hypotheses or arbitrary definitions of the modulus.

For any tuple A of k≥2 matrices, put R=|Σ A_j| and T=Σ |A_j|. The actual finite identity to prove is

```math
k(T+kI/4-R)
=k\sum_j(|A_j|-|A_j|^2)
+\frac12\sum_{i,j}(A_i-A_j)^*(A_i-A_j)
+(R-kI/2)^2.
```

The sum is over all ordered pairs, including the zero diagonal terms; half this sum equals the manuscript's unordered-pair sum. Its matrix value is `k Σ A_j* A_j − (Σ A_j)*(Σ A_j)`. It is PSD without any contraction hypothesis. The final square is PSD because R−kI/2 is Hermitian. The first sum is PSD under the original contraction hypotheses, by the preceding modulus theorem. Scaling by the strictly positive k then proves admissibility of k/4. No external Bourin–Lee theorem, operator-monotone square-root bound or Cauchy–Schwarz inequality may be imported as an unproved axiom.

The exact square identity avoids numerical eigenvalue calculations and avoids introducing an unnecessary noncommutative order inequality for square roots.

## Exact lower-bound construction

For every k≥2 define the actual complex number

```math
\omega=\exp(2\pi i/k),\qquad
v_j=\begin{pmatrix}1/2\\(\sqrt3/2)\omega^j\end{pmatrix},\qquad
A_j=e_1v_j^*,\quad 0\le j<k.
```

The generic roots-of-unity obligations are ||ω||=1 and Σ ω^j=0 for the entire k-element index set. These must hold for arbitrary natural k≥2, including odd k=3; no bounded enumeration of k is sufficient. The pinned actual primitive-root theorem and finite geometric-sum theorem are suitable exact library inputs.

The only scalar algebraic normalization is `(sqrt 3)^2=3` with `sqrt 3≥0`, giving `(1/2)^2+(sqrt 3/2)^2=1`. Prove the actual vectors have Euclidean norm one and each actual matrix A_j has induced operator norm one. Prove the genuine modulus identity |A_j|=v_jv_j* using PSD positivity and the actual square-root identity/uniqueness; a supplied rank-one-modulus table is not allowed.

The required exact sums are

```math
\sum_j A_j=\frac{k}{2}e_1e_1^*,\qquad
\sum_j|A_j|=\begin{pmatrix}k/4&0\\0&3k/4\end{pmatrix},
```

and, for the actual modulus of the first sum,

```math
\left|\sum_j A_j\right|-\sum_j|A_j|
=\begin{pmatrix}k/4&0\\0&-3k/4\end{pmatrix}.
```

For any proposed admissible c, specialize its **actual** universal property to n=2 and this contraction tuple, and evaluate the PSD difference on e1 (or its actual first diagonal entry). This gives c−k/4≥0. Together with the complete upper bound it proves IsLeast and the actual infimum equality. Specialization to odd k≥3 then proves the original statement with all quantifiers preserved.

## Computation, trust and intended scope

Use symbolic finite sums, actual CFC identities and exact root-of-unity facts. There are no approximate roots or spectra, interval boxes, exhaustive unitary searches, finite-dimensional cutoffs or extrapolations from sampled k. The exact proof needs **no numerical interval certificate**. LeanCert will perform explicit `#assert_trust kernel` audits of the actual exported proof and its transitive dependencies; this role must be described truthfully rather than represented as an interval calculation. No decorative scalar certificate is required.

The eight selected exports are `modulus_semantics`, `contraction_modulus`, `positive_decomposition`, `universal_upper_bound`, `root_of_unity_data`, `sharpness_witness`, `sharp_constant` and `odd_contraction_conjecture`, all under `NLA.MI03`. Every advertised bridge is a conclusion. The source's additional three-dimensional Hermitian extremizers and a formal theorem about the witness rank are outside these exports; neither is part of the canonical question.

Pin Lean 4.33.1, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Follow the campaign's Schiffer/Forsythe structure and credit any actual reuse. Two final proof referees must check source correspondence, actual definitions/instances and consumed dependencies using the appropriate Tau Ceti rubrics. Real Linux Comparator with empty definition exceptions, default-kernel replay, permitted-axiom checks, truthful v0.4 metadata and a separate operational/publication audit remain later gates. Only `propext`, `Classical.choice` and `Quot.sound` may support the theorem.
