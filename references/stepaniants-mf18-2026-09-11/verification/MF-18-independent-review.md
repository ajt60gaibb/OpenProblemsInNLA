# Independent mathematical review of the MF-18 solution

**Verdict: PASS for the complete canonical complex-coefficient MF-18 target, under its stated hypotheses.**

Reviewer: the separate Codex agent `prepare_manuscripts`, 11 September
2026. This is an independent agent review, not external human peer
review, formal verification, or a historical-priority determination.

## Exact reviewed version

The frozen manuscript is `RESULT.md`, 10,665 bytes, SHA-256
`dc6fb4b1b4c8d1fc2d841b35165e708d21d8f228dfdf18402e5845a9f29fcfd7`.
The entire shortened version was read and independently reconstructed.
The earlier 12,194-byte draft was snapshotted before revision as
`independent-initial-snapshot.md`, SHA-256
`d355e2f2e7fdfad8e74385074bb1be298c960a17b4d71de08d57e84bb063cf91`.
This verdict is bound to the shortened version, not merely to the earlier
draft or an author's summary.

The canonical statement was read at
`/tmp/nla-mf18-worktree/matrix-functions-and-stability/MF-18/README.md`.
It asks for the rank equality with general complex \(C,D\), Hermitian
\(R,P\), a finite invertible stabilizing limit, and algebraically simple
unit-circle polynomial roots. The manuscript retains all of these
hypotheses. It does not replace the target by the existing real,
scalar-regularization auxiliary theorem.

## Primary-source verification

The [JCAM author manuscript](https://uregina.ca/~chguo/JCAM_GuoKuoLin.pdf)
was checked directly. Equation (1), manuscript page 1, has the same
complex equation and positivity hypothesis. Its Theorems 2–3 give the
stable spectral selection and solution setting; Theorem 5, manuscript
pages 7–8, states the imaginary-part rank upper bound. The paragraph
immediately following its proof poses equality when the unit-circle
eigenvalues are simple. Thus the manuscript addresses the cited
conjecture. The new proof re-establishes the root-count facts it needs
and supplies the lower bound; it does not assume the conjectured equality.
The [published record](https://doi.org/10.1016/j.cam.2012.05.012)
identifies the same paper and bibliographic details.

The review does not independently certify an exhaustive public-network
or literature-priority search. The coordinating agent owns that check.

## 1. Perturbed polynomial and exact stable selection

The positive-definite matrix required on the unit circle is
\(W(\lambda)=P-\lambda D^*-\lambda^{-1}D\). It follows from the
given hypothesis by replacing \(\lambda\) with \(-\lambda\), and
\(P\succ0\) follows by averaging the two signs. This works for
general complex \(D\).

In the homotopy of Lemma 2, the matrix
\(\lambda^{-1}\mathcal P_{\eta,t}(\lambda)\) has Hermitian real
part and negative-definite Hermitian imaginary part on the unit circle.
It is therefore nonsingular there. The determinant is not identically
zero at any homotopy parameter, and its boundary winding number is
constant. At \(t=0\) it is the determinant of \(-i\eta\lambda P\),
which has exactly \(n\) zeros at zero. The argument principle thus
gives the claimed \(n\) interior zeros even if the determinant degree
changes along the homotopy. No leading or constant coefficient needs
to be invertible.

Expanding the factorization gives respectively
\(B_\eta\), \(-B_\eta S_\eta-X_\eta=-Q_\eta\), and
\(X_\eta S_\eta=A_\eta\). All matrix orderings in that expansion
are correct. Since \(\det(\lambda I-S_\eta)\) already contributes
\(n\) interior zeros, the other determinant factor has none.

The finite nonsingular limit guarantees convergence of inverses and
therefore coefficientwise convergence of that first factor to
\(\ell_0\). Its nonzero constant value \((-1)^n\) rules out the
identically-zero limit. Uniform convergence on a small circle and
Rouché's theorem prohibit an interior zero from appearing in the
limit. Consequently the limiting factorization identifies *all*
interior roots of \(\mathcal P_0\) with those of \(S\), with the
same algebraic multiplicities. No differentiability of \(X_\eta\)
or analytic selection of its eigenvectors is being assumed.

## 2. Singular leading coefficients and the unit-circle count

The scalar determinant identity

\[
p(\lambda)=\lambda^{2n}\overline{p(1/\overline\lambda)}
\]

is valid because \(R=R^*\) and the leading and constant coefficients
of the matrix polynomial are \(C^*\) and \(C\). If \(d\) is its
degree and \(z\) its order of vanishing at zero, coefficient reversal
gives \(d+z=2n\). This explicitly accounts for possible degree loss
when \(C\) is singular; treating the determinant as degree exactly
\(2n\) would have been an error, but the manuscript does not do so.

Nonzero off-circle roots occur in reciprocal-conjugate pairs with equal
multiplicities. With \(2m\) unit-circle roots, the number of interior
roots, including zero, is

\[
z+\frac{d-z-2m}{2}=n-m.
\]

The preceding factorization then forces exactly \(n-m\) stable
eigenvalues of \(S\). Continuity gives \(\rho(S)\le1\), so its
remaining \(m\) eigenvalues are on the unit circle. Any such root's
multiplicity as a root of \(\det(\lambda I-S)\) is at most its
multiplicity in \(p\), which is one. Thus these roots are distinct
and semisimple. No statement about complex-conjugate pairing of
individual unit roots is needed.

## 3. Nonvanishing boundary Gram and the lower bound

Taking Hermitian imaginary parts of
\(X+C^*X^{-1}C=R\), using the exact inverse identity, yields
\(H=S^*HS\). This identity is valid for nonsymmetric and
non-Hermitian \(X\).

For a unit eigenvector \(Sv=\lambda v\), the factorization places
\(v\) in the kernel of \(F(\theta_0)\). A simple determinant zero
implies nullity one: higher nullity would make its adjugate zero and
the determinant derivative zero. Since \(F(\theta_0)\) is Hermitian,
its adjugate is a nonzero real multiple of \(vv^*\). Therefore
\(a=v^*F'(\theta_0)v\ne0\). The parameterization
\(\lambda=e^{i\theta}\) has nonzero derivative at every unit root,
so simplicity is preserved, including at \(\lambda=1,-1\).

Independently substituting \(Cv=\lambda Xv\) into the derivative
gives

\[
a=i\bigl(v^*X^*v-v^*Xv\bigr)=2v^*Hv.
\]

The sign and factor of two are correct. For distinct unit eigenvalues,
the Stein identity annihilates the corresponding off-diagonal Gram
entries, because \(1-\overline{\lambda_j}\lambda_k\ne0\).
The resulting \(m\)-dimensional Gram is diagonal with nonzero entries.
It is therefore nonsingular, proving \(\operatorname{rank}H\ge m\).
This argument needs neither positivity of \(H\) nor a claim about
the direction of each individual root's perturbation.

## 4. Stable Jordan blocks and the upper bound

The generalized stable eigenspace has dimension \(n-m\). All its
Jordan blocks decay under powers, including nontrivial blocks and
nilpotent blocks at zero. The unit-circle blocks of \(S\) are simple,
so all powers of the full matrix \(S\) are bounded. For a stable
generalized vector \(x\), iteration of the Stein identity gives

\[
x^*Hy=(S^j x)^*H S^j y\longrightarrow0
\]

for every \(y\). Since \(H\) is Hermitian this implies \(Hx=0\).
Thus the kernel has dimension at least \(n-m\), and
\(\operatorname{rank}H\le m\). Combined with the lower bound, this
proves the equality. The proof does not assume diagonalizability of
the stable part. When \(m=0\), the same argument yields \(H=0\)
without a separate limiting-ratio calculation.

## Explicit edge-case sanity checks

These are independent algebraic checks, not substitutes for the proof.
For \(n=1\), take \(C=i\), \(D=R=0\), and \(P=1\). Then

\[
\mathcal P_0(\lambda)=i(1-\lambda^2),\qquad
X_\eta=\frac{i}{2}\bigl(\eta+\sqrt{\eta^2+4}\bigr).
\]

The roots \(1,-1\) are both simple, \(S_\eta=i/X_\eta\) is
strictly stable, and \(X_0=i\) has imaginary-part rank one. This
confirms that simple real unit roots are legitimate in the complex
canonical model and are covered by the derivative argument.

Adding the independent scalar block \(C=0,R=P=1,D=0\) gives a
singular overall \(C\), determinant degree three and zero order one
at \(n=2\), the same two simple unit roots, and rank one. The grade
count correctly gives one strictly interior root and one selected
boundary root. With only the latter scalar block, \(m=0\) and the
limiting imaginary part is zero. These examples also confirm that no
invertibility of \(C\) or \(D\) has been smuggled into the argument.

## Conclusion and limits

No mathematical correction is required for the frozen version. Its
proof addresses the entire stated complex-coefficient, simple-unit-root
question, while preserving the existing Colbrook auxiliary contribution's
separate attribution and scope. The finite nonsingular stabilizing limit
is a hypothesis, not proved to exist here. Defective or repeated unit
roots remain outside the canonical theorem and outside this review.

No numerical search, floating-point eigenvalue test, or computer algebra
certificate is used in the proof. Standard finite-dimensional spectral
facts, the argument principle, and Rouché's theorem are the external
mathematical tools used. This review authorizes no repository or public
status mutation by itself; the coordinating agent handles openness,
faithful source conversion, rendering, and the user's submission workflow.
