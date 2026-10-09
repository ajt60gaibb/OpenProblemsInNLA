# MI-15 — A sum-of-squares representation for the Toeplitz commutator form

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Provenance:** explicit conjecture  
**Status:** Lean verified

**Last checked:** 2026-10-08

**Rating rationale:** These ratings are historical and refer to the original universal conjecture: all-order algebraic certification required more than known nonnegativity, with direct application to a specific Toeplitz commutator form. They do not rate the remaining finite-order questions.

## Resolution — 2 October 2026

**Resolved negatively.** Wenqi Zhu (Mathematical Institute, University of Oxford) and Ping Nie (David R. Cheriton School of Computer Science, University of Waterloo).

The answer is **no**: for every integer $`n\ge2^{9961475}`$, the original polynomial $`F_n`$ is not a finite sum of squares of real homogeneous quadratic forms, allowing arbitrary real coefficients and any finite number of squares. This refutes the universal assertion below. The strengthened Böttcher–Wenzel inequality still gives $`F_n\ge0`$ for every input at every order.

Zhu and Nie's [arXiv preprint, posted 6 October 2026](https://arxiv.org/abs/2610.08980) presents the negative theorem, the exact positive range through order 50, and a further all-order positive result: if either Toeplitz factor is symmetric or skew-symmetric, the restricted form is SOS while the other factor is any real Toeplitz matrix. The symmetry-subclass result is cited from the preprint; the Lean evidence below concerns the unrestricted negative theorem and positive orders through 20. The paper discloses AI assistance in developing candidate constructions, code and arguments; the authors state that they reviewed the work and take responsibility for the publication.

Lean proves SOS for every $`2\le n\le20`$. Exact rational Gram certificates, checked for polynomial identity and positivity by the project's [positive certificate checker](https://github.com/erenup/toeplitz-bw-not-sos/blob/7126c0841b008dc89a21edfd008bbf1b748d280f/verification/positive.py), establish SOS for every $`2\le n\le50`$. The range through 50 is exact computational evidence; the Lean positive theorem covers the range through 20.

The unresolved gap is $`51\le n<2^{9961475}`$. The smallest bad order and a smaller explicit obstruction threshold remain open. No assertion that every gap order has the same answer is made. See the [Lean proof and verification evidence](#lean-proof-and-verification-evidence) for the formal resolution and the two positive evidence scopes.

## Lean proof and verification evidence

### Immutable source and dependencies

The [proof repository at `7126c0841b008dc89a21edfd008bbf1b748d280f`](https://github.com/erenup/toeplitz-bw-not-sos/tree/7126c0841b008dc89a21edfd008bbf1b748d280f) pins Lean **`v4.34.0-rc2`** in its [toolchain file](https://github.com/erenup/toeplitz-bw-not-sos/blob/7126c0841b008dc89a21edfd008bbf1b748d280f/lean/lean-toolchain), and Mathlib **`85e3a25e006c35636f0e53b0e9296caca2685bc0`** in its [dependency manifest](https://github.com/erenup/toeplitz-bw-not-sos/blob/7126c0841b008dc89a21edfd008bbf1b748d280f/lean/lake-manifest.json). That manifest pins the remaining dependencies as well.

### Declarations and statement correspondence

The following definitions are in [`lean/ToeplitzSOS/Defs.lean`](https://github.com/erenup/toeplitz-bw-not-sos/blob/7126c0841b008dc89a21edfd008bbf1b748d280f/lean/ToeplitzSOS/Defs.lean), in namespace `ToeplitzSOS`:

- **Variables:** `V n = CoordFamily × Fin (2 * n - 1)`. The two constructors of `CoordFamily` select `x` and `y`; the second coordinate $`a=0,\ldots,2n-2`$ encodes the signed diagonal $`a-(n-1)`$. Thus `MvPolynomial (V n) Real` has exactly the independent real variables $`x_{-(n-1)},\ldots,x_{n-1},y_{-(n-1)},\ldots,y_{n-1}`$ in the original $`4n-2`$-variable polynomial ring.
- **Toeplitz matrices:** `X n` and `Y n` use `diagIndex i j = i + (n - 1 - j)` for `i j : Fin n`. Since $`0\le j< n`$, this is the offset encoding of $`i-j`$. Moving from zero-based to one-based matrix indices leaves the difference unchanged, giving exactly the catalogue's $`X=(x_{i-j})`$ and $`Y=(y_{i-j})`$.
- **Norm and polynomial:** `frob A` is $`\sum_{i,j}A_{ij}^2`$; `inner A B` is $`\sum_{i,j}A_{ij}B_{ij}=\mathop{\mathrm{tr}}\nolimits(A^TB)`$. Therefore `toeplitzBW n` is precisely the displayed $`F_n`$, with the two coefficients 2 and the ordinary matrix commutator. These are squared Frobenius norms over the real coefficient ring.
- **Squares and identity:** `IsSumSqHomQuad p` asserts that there exist a natural number `s` and `q : Fin s → MvPolynomial (V n) Real` such that each `q j` satisfies `IsHomogeneous 2` and $`p=\sum_j(q_j)^2`$ in that polynomial ring. The count may be zero, is finite, and is unrestricted; the real coefficients and the square count may depend on $`n`$. This is a polynomial identity, not equality at finitely many inputs or a constraint on a selected Gram ansatz.
- **Universal quantifier:** `MI15` is `∀ n ≥ 2, IsSumSqHomQuad (toeplitzBW n)`, precisely the original assertion for every integer order $`n\ge2`$.

In namespace `ToeplitzSOS.Negative`, the [statement file](https://github.com/erenup/toeplitz-bw-not-sos/blob/7126c0841b008dc89a21edfd008bbf1b748d280f/lean/ToeplitzSOS/Negative/SharpStatement.lean) defines `SharpNegativeResolution`. Its theorem `sharpOrderThreshold_eq` identifies the symbolic threshold with $`2^{9961475}`$, and `sharpNegativeResolution_iff_explicit` expands the finite real homogeneous-quadratic quantifiers. The [resolution file](https://github.com/erenup/toeplitz-bw-not-sos/blob/7126c0841b008dc89a21edfd008bbf1b748d280f/lean/ToeplitzSOS/Negative/Resolution.lean) proves:

- `ToeplitzSOS.Negative.sharpNegativeResolution`: the unconditional all-larger-order non-SOS statement.
- `ToeplitzSOS.Negative.sharp_negative_explicit`: the same theorem with the square count, real coefficient polynomials, degree-two homogeneity and polynomial identity expanded.
- `ToeplitzSOS.Negative.not_MI15`: the negation of the catalogue's universal assertion.

All analytic premises needed for these conclusions are proved within the import closure; they are not extra assumptions on the catalogue problem. The word `sharp` in declaration names distinguishes sufficient bounds and does not claim an optimal threshold.

For the positive range, [`ToeplitzSOS.toeplitzBW_isSumSq_of_le_20`](https://github.com/erenup/toeplitz-bw-not-sos/blob/7126c0841b008dc89a21edfd008bbf1b748d280f/lean/ToeplitzSOS/Certificates/Range.lean) proves exactly $`2\le n\le20`$ for the same polynomial and SOS predicate. The separate [exact certificate documentation](https://github.com/erenup/toeplitz-bw-not-sos/blob/7126c0841b008dc89a21edfd008bbf1b748d280f/verification/README.md#positive-orders) describes the rational chain through order 50.

### Reproduction and verification record

The dated successful build and verification log is [`VERIFICATION.md`](https://github.com/erenup/toeplitz-bw-not-sos/blob/7126c0841b008dc89a21edfd008bbf1b748d280f/VERIFICATION.md). It records the verification of the declarations above and their dependencies. **The catalogue did not rerun the checks**; the evidence supplied for this status is the external project's verification record.

With the pinned Lean toolchain installed, run from the repository root of the pinned revision:

```
cd lean
lake exe cache get
./verify
./verify --certificates
```

The first verification command builds and audits the negative theorem and its dependencies. The second also builds and audits the positive certificates and range theorem. Dependency pins must be retained. For the exact positive range through 50, follow the [dependency setup and commands](https://github.com/erenup/toeplitz-bw-not-sos/blob/7126c0841b008dc89a21edfd008bbf1b748d280f/verification/README.md) and run from the repository root:

```
python3 -m venv .venv
.venv/bin/python -m pip install -r verification/requirements.txt
.venv/bin/python verification/positive.py
.venv/bin/python -O verification/positive.py
```

### Transitive axioms

The [verification record](https://github.com/erenup/toeplitz-bw-not-sos/blob/7126c0841b008dc89a21edfd008bbf1b748d280f/VERIFICATION.md) contains the transitive axiom report for the target declarations. Only `propext`, `Classical.choice` and `Quot.sound`, or a subset, are allowed. The project's [audit](https://github.com/erenup/toeplitz-bw-not-sos/blob/7126c0841b008dc89a21edfd008bbf1b748d280f/lean/Audit.lean) traverses every imported project declaration, including private and generated declarations; its [verifier](https://github.com/erenup/toeplitz-bw-not-sos/blob/7126c0841b008dc89a21edfd008bbf1b748d280f/lean/verify) rejects other axioms and exercises corrupted-source and unproved-axiom controls. No `sorryAx`, unproved custom axiom or additional trust in native execution supports the target theorems.

The Lean declarations are the primary references for the formal resolution. The [arXiv paper, *Sum-of-Squares and Non-Sum-of-Squares Regimes for the Toeplitz Böttcher–Wenzel Form*](https://arxiv.org/abs/2610.08980) gives the mathematical exposition and the all-order symmetry-subclass result. The [paper–Lean map](https://github.com/erenup/toeplitz-bw-not-sos/blob/7126c0841b008dc89a21edfd008bbf1b748d280f/paper-lean-mapping/README.md) distinguishes its formalized statements and exact computations.

## Finite-order SOS certificates — 12 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Submission and verified affiliation](../../references/holden-matrix-2026-09-12/README.md).

Sections 1–5 of the [proof](../../references/holden-matrix-2026-09-12/MI-15/proof.md) establish sum-of-squares representations for orders $`n=8,9,10,11,12`$, with at most $`2(n-1)^2`$ homogeneous quadratic squares. The five rational Gram certificates passed exact polynomial-identity and integer positive-definiteness checks. These finite-order certificates preceded the negative resolution above.

## Problem statement

For an integer $`n\ge2`$, let $`x_{-(n-1)},\ldots,x_{n-1},y_{-(n-1)},\ldots,y_{n-1}`$ be independent real variables. Form real Toeplitz matrices $`X=(x_{i-j})_{i,j=1}^n`$ and $`Y=(y_{i-j})_{i,j=1}^n`$, and the homogeneous quartic polynomial

```math
F_n(x,y)=2\|X\|_F^2\|Y\|_F^2
-2\bigl(\mathop{\mathrm{tr}}\nolimits(X^TY)\bigr)^2-\|XY-YX\|_F^2,
```

where $`\|Z\|_F^2=\sum_{i,j}z_{ij}^2`$ for real matrices. Is it true that for every $`n\ge2`$ there are a finite integer $`N_n\ge0`$ and homogeneous quadratic polynomials $`q_{n,1},\ldots,q_{n,N_n}`$ with real coefficients in these $`4n-2`$ variables such that

```math
F_n(x,y)=\sum_{j=1}^{N_n}q_{n,j}(x,y)^2
```

as a polynomial identity? The polynomials may depend on $`n`$. Rational coefficients are not required.

## Relevance

An explicit sum-of-squares identity would give an algebraic certificate for a structured matrix inequality and connects Toeplitz calculations to semidefinite optimization. Nonnegativity alone does not answer this question.

## References

1. L. László, *Sum of squares representation for the Böttcher–Wenzel biquadratic form*, Acta Universitatis Sapientiae, Informatica 4(1) (2012), 17–32: equation (1), §5, and Conjecture 15, p.31. [Primary manuscript](https://arxiv.org/pdf/1207.6372).
2. J. Ge, F. Li, Z. Tang, and Y. Zhou, *A survey on the DDVV-type inequalities*, Advances in Mathematics (China) 53 (2024), 449–467: published Conjecture 4.1, p.461; Conjecture 4.3 in [arXiv:2402.01085v1](https://arxiv.org/html/2402.01085v1). [Published PDF](https://ccj.pku.edu.cn/Article/DownLoad?id=374327987&type=ArticleFile).
3. W. Zhu and P. Nie, *Sum-of-Squares and Non-Sum-of-Squares Regimes for the Toeplitz Böttcher–Wenzel Form*, arXiv:2610.08980v1 (2026), Theorems 2.1, 3.1 and 4.1. [Preprint](https://arxiv.org/abs/2610.08980).

## Historical status check — 2026-09-10

The following dated record predates the resolution above.

Both arXiv records remain v1; the published 2024 survey still poses this SOS assertion. László's particular certificate strategy works through order seven; its failure in a larger order is not a disproof of all SOS representations. Searches used `Toeplitz SOS Wenzel`, `Toeplitz Bottcher squares proof`, and `Toeplitz Conjecture 15 squares`. No general proof or non-SOS counterexample was located. The already proved Böttcher–Wenzel nonnegativity statement is not being counted again. The optional rational-certificate request in the original is not imposed as an additional conjecture.

**Audit update (2026-09-10):** Rechecked the survey’s Conjecture 4.3 and searched for later Toeplitz SOS results. The general assertion remains a conjecture; known small-order certificates do not establish all-order representability. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
