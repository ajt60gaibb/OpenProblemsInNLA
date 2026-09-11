# SF-01 independent proof and scope review

Review date: 2026-09-11. This is an independent mathematical audit of the complete submitted source, not acceptance of the submission's own verification labels. No manuscript or canonical problem was edited in this review.

## Verdict and exact target

**PASS: the manuscript proves the canonical SF-01 assertion. Recommend changing SF-01 from partially resolved to resolved on mathematical grounds, with the precise real, nonsingular, positive-diagonal hypotheses retained.** This verdict is not a claim of novelty, authorship, or publication priority.

The canonical file is `matrix-functions-and-stability/SF-01/README.md`. Its iteration is

\[
X_0=A,\qquad X_{k+1}=\tfrac12(X_k+X_k^{-1}A),
\]

for a real nonsingular H-matrix A with positive diagonal, and its question is whether every iterate is a nonsingular H-matrix with positive diagonal. The manuscript's Theorem 1 applies with alpha=0, beta=1, and every scaling parameter equal to one. Every iterate is a rational function of A, so the order of the commuting factors A and X_k inverse agrees with the canonical recurrence. There is no initialization or diagonal-normalization mismatch. The proof works in every finite dimension, including reducible inputs and defective matrices.

The manuscript additionally proves the assertion for every nonzero nonnegative affine initialization, arbitrary positive scalar scaling at each step, a componentwise comparison with the corresponding M-matrix iteration, and a single positive diagonal similarity yielding strict row diagonal dominance of the entire sequence. Its Halley corollary also passes. Neither convergence for arbitrary scaling nor floating-point stability is claimed or established. The theorem does not cover arbitrary commuting H-matrix initializations, singular H-matrices, complex H-matrices, or inputs with unrestricted diagonal signs. None of these is a remaining case of the stated canonical question.

## Source identification and complete coverage

Reviewed source: `.cache/colbrook-research-submission/nla_research/submission/SF-01/manuscript.tex`.

Full-source normalized SHA-256:

`058b3f2b3de6f6438237a18c8442fa93808b9c648ca3569ec57fd3c07bb0cbc1`

Normalization: decode the entire file as UTF-8, replace CRLF by LF, then encode as UTF-8 and hash. No whitespace trimming, extraction of theorem bodies, or other normalization. The normalized source contains 12,577 bytes. The standalone source includes its definitions and bibliography; no external mathematical preamble is required.

The audit covers the abstract, all definitions, Theorem 1 (`thm:newton`, line 29), Lemma 2 (`lem:closure`, line 55), Lemma 3 (`lem:resolvent`, line 80), Theorem 4 (`thm:preserver`, line 94), the proof of Theorem 1, Corollary 5 (`cor:halley`, line 134), and all scope examples and literature claims in the final section (line 161 onward). Line numbers refer to the complete reviewed source.

## Independent proof audit

### Rational-function closure: PASS

The class consists of nonzero functions

\[
f(z)=a+bz+\sum_j w_j\frac{z}{z+t_j},\qquad
a,b\geq0,\quad w_j,t_j>0.
\]

Positive linear combinations stay in the class. The nontrivial operation is f to z/f. For a nonconstant member, its imaginary part has exactly the sign of the imaginary part of z, because the multiplier is b plus a sum of strictly positive terms w_j t_j/|z+t_j| squared. Thus finite zeros are real; positivity on the positive axis excludes positive zeros. The real derivative is strictly positive away from the poles, so every zero is simple. Repeated original poles are combined first, so no artificial cancellation obscures this argument.

A zero at zero is canceled in z/f. The resulting value there is 1/f'(0)>0; otherwise that value is zero. At a negative zero -s, the residue of z/f is -s/f'(-s), which has exactly the sign and size required for a positive multiple of z/(z+s). Original poles of f become removable points or zeros. After subtracting all these terms, the polynomial remainder has degree at most one. Its linear coefficient is zero if b>0 and is 1/(a+sum w_j)>0 if b=0. Its constant coefficient is the nonnegative value at zero. This proves the stated representation. The positive-constant case and the pure linear case are valid boundary cases, not omissions.

The weighted parallel-sum identity follows by applying the already proved operations to z/f+c z/g. It is used later only with positive c. No analytic representation theorem for general Bernstein functions is needed.

### Resolvent and matrix-function comparison: PASS

Put C equal to the comparison matrix, D=diag(A)>0, and N=D-A. Then C=D-|N|. From Cv>0 with v>0, the weighted maximum norm of (D+tI) inverse times |N| is strictly below one for t>=0. Hence the Neumann expansion of (A+tI) inverse is absolutely dominated term by term by the nonnegative expansion for (C+tI) inverse. This both proves the resolvent comparison and establishes nonsingularity where needed.

For v=C inverse times the all-ones vector, the manuscript obtains

\[
f(C)v=av+b\mathbf1+\sum_j w_j(C+t_jI)^{-1}\mathbf1>0.
\]

Every summand is nonnegative; whichever coefficient is nonzero supplies strict positivity in every coordinate. A nonsingular M-matrix inverse has nonnegative entries and positive diagonal, so this remains true for reducible matrices. The representation f(C)=aI+bC+sum w_j[I-t_j(C+t_jI) inverse] also shows that f(C) is a Z-matrix. The positive-vector criterion therefore establishes that f(C) is a nonsingular M-matrix.

The diagonal estimate f(A)_ii>=f(C)_ii>0 and the off-diagonal estimate |f(A)_ij|<=-f(C)_ij follow directly from the resolvent comparison and the sign of b. They yield comparison(f(A))>=f(C). Applying this inequality to the same v proves that f(A) is an H-matrix with positive diagonal. This is a structured argument for rational functions of one input; it does not assume false closure properties for sums or products of unrelated H-matrices.

### Newton recurrence, comparisons, and common similarity: PASS

The initial scalar function alpha+beta z belongs to the class even when exactly one coefficient is zero. The update is a positive sum of f and z/f, with respective factors mu/2 and 1/(2mu). Closure therefore proves that every scalar iterate is in the class for any sequence of finite positive mu values. The matrix-function theorem supplies invertibility before the next inverse is taken, so existence of the matrix recurrence is not inferred merely from formal cancellation of rational expressions.

Using the same numerical scalars in the comparison recurrence gives Y_k=f_k(C), and hence comparison(X_k)>=Y_k. The fixed vector v=C inverse times one satisfies Y_k v>0 for all k. Dividing comparison(X_k)v>0 coordinatewise by v_i gives precisely strict row diagonal dominance of diag(v) inverse X_k diag(v), with positive diagonal. This is one similarity for the entire sequence, not a new weight chosen at each step.

### Halley and its displayed denominator: PASS

With g=z/f, direct algebra gives

\[
\frac{f(f^2+3z)}{3f^2+z}
=\frac13f+\frac83(f^{-1}+3g^{-1})^{-1}.
\]

The right-hand side is in the same class; replacing f by mu f handles each positive scaling. A separate check is essential because rational closure alone would not establish invertibility of the denominator actually used in the matrix algorithm. The source supplies this check correctly.

The fixed diagonal similarity makes A strictly row diagonally dominant with positive diagonal, so Gershgorin places its spectrum in the open right half-plane. Every nonzero member f of the rational class has strictly positive real part there, including the constant and linear boundary cases. The same holds for g=z/f. Thus 1/f+3/g has positive real part and cannot vanish. Since it equals (z+3f squared)/(zf), the displayed denominator 3f squared+z has no zeros on the spectrum of A. Rational spectral mapping proves matrix invertibility, including for non-diagonalizable A. The remaining comparison and common-weight conclusions now follow from Theorem 4.

### Scope counterexample: PASS

For the final example A=[[-1,3],[-1/10,-1]], its comparison matrix has eigenvalues 1 plus or minus sqrt(3/10), both positive, and is a nonsingular M-matrix. The eigenvalues of A are -1 plus or minus i sqrt(3/10), avoiding the nonpositive real axis, so its principal square root is defined. Starting Newton at I gives [[0,3/2],[-1/20,0]], whose comparison matrix cannot be a nonsingular M-matrix. Thus removing the positive-diagonal assumption fails even when the principal square root exists. This example concerns the explicitly discussed extension with X_0=I and does not weaken the main theorem.

## Primary-source comparison

The following primary sources were accessed on 2026-09-11. Their scope was checked independently; citation or metadata agreement is not a priority determination.

- [Guo, author preprint of the 2010 LAA paper](https://uregina.ca/~chguo/laa7.pdf): Section 7, Proposition 22 and its following paragraph explicitly discuss the unnormalized M-matrix question for X_0=I. Propositions 23–24 transfer the normalized result to H-matrices. The submitted theorem does answer that stated unnormalized question and also includes the repository's X_0=A initialization. The preprint's printed page 20 locator is consistent with the cited paragraph.
- [Guo and Lu, arXiv:1807.04251](https://arxiv.org/pdf/1807.04251): Section 4 and Theorem 11 concern the normalized H_1/M_1 classes, diagonal entries in (0,1], and X_0=I. Their broader Schroeder-family result is acknowledged accurately. The submitted square-root result does not claim the entire Schroeder-family extension.
- [Kouba, arXiv:1104.4175](https://arxiv.org/pdf/1104.4175): the paper gives scalar partial-fraction formulas for Newton and Halley square-root iterations. These provide relevant precedents, and the manuscript expressly leaves priority of its precise extensions open.
- [Higham's official errata](https://nhigham.com/errata-for-functions-of-matrices-theory-and-computation/): the corrections to the surrounding H-matrix discussion specify real matrices. The submitted real setting agrees with the canonical correction.
- [Bini, Iannazzo, Meini, and Meng, arXiv:2605.21679v1](https://arxiv.org/html/2605.21679): Section 4 assumes the normalized M-matrix representation A=I-C, C>=0, after a scalar reduction. Its triplet algorithms and numerical stability results do not themselves establish the full unnormalized positive-diagonal H-matrix assertion audited here.

## Independent checks and limits

Besides the universal proof audit above, an independent standard-library exact-rational diagnostic used

\[
A=\begin{pmatrix}2&3\\1/10&1\end{pmatrix},\qquad
C=\begin{pmatrix}2&-3\\-1/10&1\end{pmatrix}.
\]

Starting at A and C, respectively, it performed three Newton steps and, separately, three Halley steps with mu=2, 1/2, 3/2. Exact Fraction arithmetic checked every inverse, positive diagonals, nonpositive off-diagonal entries of the comparison iterates, the full entrywise comparison inequality, and Y_k v>0 for v=C inverse times one. Both runs passed. This input is not a Z-matrix and has an unnormalized diagonal. These finite calculations only corroborate the algebra; they are not evidence for untested dimensions or an alternative to the proof.

No substantive gap, missing canonical case, or necessary source correction was found. Exact-arithmetic structure preservation is established; numerical stability, arbitrary-scaling convergence, and priority are outside this verdict.
