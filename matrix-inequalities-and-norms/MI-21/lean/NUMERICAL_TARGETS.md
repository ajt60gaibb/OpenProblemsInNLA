# MI-21 statements and numerical obligations — stage 1

No proof implementation has begun. The definitions and three Challenge exports below must receive two independent statement approvals before proof work. The canonical problem ID, path and mathematical target are retained.

## Complete original target

The canonical entry at upstream revision `e7252e5307781a7c897bca6cb124f6ab838f6809` asks whether, for every pair of positive integers `m,n`, every two families `Aᵢ,Bᵢ ∈ ℂⁿˣⁿ` of Hermitian positive definite matrices, every real `t ∈ [0,1]` and `s,r,p > 0` with `sr ≥ 1`, and **every unitarily invariant complex matrix norm** `ν`,

\[
\nu\left(\sum_{i=1}^m(A_i^s\#_t B_i^s)^r\right)
\le
\nu\left(\left(A^{(1-t)srp/2}B^{tsrp}A^{(1-t)srp/2}\right)^{1/p}\right),
\quad A=\sum_i A_i,\quad B=\sum_i B_i.
\]

The actual weighted mean is

\[
X\#_tY=X^{1/2}(X^{-1/2}YX^{-1/2})^tX^{1/2}.
\]

All matrix powers are real spectral powers on positive definite matrices. They must not be interpreted entrywise or replaced by unspecified candidate roots.

`GeometricMeanNormConjecture` retains every quantifier and assumption above. `IsUnitaryInvariantNorm ν` spells out nonnegativity, definiteness, triangle inequality, absolute homogeneity for every complex scalar, and independent left/right unitary invariance. Thus the universal norm quantifier includes all unitarily invariant norms, not merely the operator norm. A unitary is characterized by its two conjugate-transpose inverse identities. Summands use `Fin m`; matrix indices use `Fin n`.

## Semantic boundary

- `spectralPower X q := CFC.rpow X q` uses Mathlib's actual continuous functional calculus and its real exponent. There is no local root oracle or diagonalization assumption.
- `geometricMean`, `leftMatrix`, and `rightMatrix` keep the original order of every noncommuting factor. In particular the right exponent is `(1-t)*s*r*p/2`, the middle exponent is `t*s*r*p`, and the final exponent is `1/p`.
- Positive definiteness is `Matrix.PosDef` over `ℂ`, including Hermitian symmetry and the strictly positive quadratic form. No weaker real-only input class replaces the universal complex class.
- `operatorNorm X := ‖Matrix.toEuclideanCLM X‖` is the actual operator norm on complex Euclidean space, not the default entrywise matrix norm or an assumed eigenvalue.
- `operatorNorm_isUnitaryInvariant` must prove that this concrete norm satisfies every norm axiom in `IsUnitaryInvariantNorm`, in every dimension. The final contradiction may then legitimately instantiate the universal norm quantifier.
- The explicit rational matrices below are candidate identities to prove from the actual CFC expressions. They are not assumptions in the target or counterexample.

## Exact witness

Use `m=n=2`, `s=t=1/2`, `r=2`. Then `sr=1`. The counterexample export quantifies over every real `p>0`; a single choice such as `p=1` already refutes the full target.

\[
C=\operatorname{diag}(12/37,21/29),\qquad
E=\operatorname{diag}(35/37,20/29),\qquad
S=\frac1{17}\begin{pmatrix}15&8\\8&-15\end{pmatrix},
\]
\[
A_1=C^2,\quad A_2=E^2,\quad B_1=SE^2S,\quad B_2=SC^2S.
\]

Necessary finite obligations are `C,E` positive definite, `Sᴴ=S`, `S²=I`, and `C²+E²=I`. Therefore all four actual inputs are complex Hermitian positive definite and their aggregate sums are both `I`. The actual right matrix must equal `I` for every `p>0`, hence its actual operator norm is `1`.

For the geometric-mean computation, the source gives these intermediate obligations (not new hypotheses):

\[
D=SES,\quad \delta=5/3,\quad
h=61697295/8682716,\quad
D+\delta C=\frac1{310097}
\begin{pmatrix}443355&33000\\33000&605715\end{pmatrix},
\]
\[
(C\#D)^2=\frac1{12158163}
\begin{pmatrix}3516940&616000\\616000&6547660\end{pmatrix}.
\]

The squared mean formula must be derived for these genuine CFC powers, for example by proving the source's positive-root identity or its equivalent Riccati identity and root uniqueness. Merely checking the rational arithmetic while assuming this CFC identity would leave the target unresolved. The second summand must also be derived; the source uses symmetry and unitary covariance of the geometric mean.

The combined actual left matrix must be

\[
L=\frac1{12158163}
\begin{pmatrix}8216600&-985600\\-985600&11912600\end{pmatrix}.
\]

For the explicitly nonzero complex Euclidean vector `w=(1,-4)`, the exact eigenvector equation is

\[
Lw=\lambda w,\qquad \lambda=1351000/1350907.
\]

The actual operator-norm definition then gives `λ ≤ ‖L‖₂`. Computing its entire singular spectrum is unnecessary. The sole proposed LeanCert point certificate is

\[
1<1351000/1350907=1+93/1350907.
\]

All other numerical obligations are exact finite rational/complex algebra and positivity. No interval subdivision, large parameter box, rounded eigenvalue, multidimensional root search, or extra numerical trust is needed. The planned minimal proof-only LeanCert import is `LeanCert.Tactic.IntervalAuto.PointIneq`, using explicit kernel mode.

## Three final declarations required

1. `operatorNorm_isUnitaryInvariant (n : ℕ)` proves the concrete norm's admissibility, with no assumed norm or invariance facts.
2. `counterexample (p : ℝ) (hp : 0 < p)` proves the four inputs' positive definiteness, both aggregate identities, equality of the actual left expression to `L`, equality of the actual right expression to `I`, the nonzero-vector eigenvalue equation, the strict rational gap, the actual operator-norm lower bound and strict inequality.
3. `not_geometricMeanNormConjecture` proves the full logical negation of the original universal target by choosing the witness and the concrete admissible operator norm. It is not a conditional statement and does not assume any manuscript theorem.

`Challenge.lean` contains three deliberate theorem holes, exclusively for trusted statement comparison; no proof module or Solution exists at this stage. All eventual proof exports must have transitive axiom dependencies contained in `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`, custom axioms or native execution trust. No narrower proved parameter regime in the source literature is challenged, and no mathematical novelty or human peer review is claimed.

## Attribution

Mathematical counterexample and source proof: Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Lean formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. Source mathematical authorship is not reassigned to the formalization author.
