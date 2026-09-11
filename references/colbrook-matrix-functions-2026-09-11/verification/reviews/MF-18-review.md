# MF-18 independent proof and scope review

Review date: 2026-09-11. This audit reads the complete submitted source and checks its arguments independently of supplied verification labels. No proof or canonical problem was edited.

## Verdict and exact status recommendation

**PASS for the manuscript's real, scalar-regularized Riccati theorem and its stated corollary and examples. NOT a resolution of the canonical MF-18 question. Recommend retaining MF-18 as partially resolved and recording this manuscript only as an auxiliary result for the real setting.** No novelty, authorship, or priority claim follows from this proof review.

The canonical target in `matrix-functions-and-stability/MF-18/README.md` permits general complex C,D,R,P, with R,P Hermitian and P+lambda D*+lambda inverse D positive definite on the unit circle. Its equation is

\[
X_\eta+(C^*+i\eta D^*)X_\eta^{-1}(C+i\eta D)=R+i\eta P.
\]

Assuming a finite nonsingular limit, a regular limiting quadratic polynomial, and 2m simple unit-circle eigenvalues, it asks whether rank(Im X_0)=m. The submitted manuscript instead treats real A, real symmetric Q, D=0, and P=I, with the complex symmetric solution of X_eta+A transpose X_eta inverse A=Q+i eta I. It allows arbitrary unit-circle Jordan sizes and derives a refined count in this real setting.

Thus the submitted theorem extends the Jordan-structure analysis in a restricted model; it does not settle the missing general-complex simple-eigenvalue assertion. The simple real case in the intersection of the two formulations was already covered by the cited literature. The remaining canonical target is exactly the rank equality for general admissible complex C,D,R,P under the canonical simple-circle hypotheses. No part of this review upgrades that target to solved. Extending the argument would require additional proof: the scalar regularization preserving local eigenvectors and the real-symmetry pairing cannot be carried over by merely replacing transposes with adjoints.

## Source identification and coverage

Reviewed source: `.cache/colbrook-research-submission/nla_research/submission/MF-18/manuscript.tex`.

Full-source normalized SHA-256:

`dc1d5dbbd846aa43aa8d5990a4ce26d2ead9493a77e4033440815bda7a4eda23`

Normalization: decode the complete file as UTF-8, replace CRLF by LF, encode as UTF-8, and hash. No trimming or other normalization. The normalized source contains 22,282 bytes. This is a standalone source with its own definitions and bibliography, not a theorem excerpt.

Coverage includes all assumptions and Theorem 1 (`thm:main`, line 56), the Stein and graph identities (lines 80–121), local Rellich analysis (line 123 onward), Lemma 2 (`lem:interpolation`, line 169), construction of the full stable basis, every limiting Gram block, the real-symmetry argument, Corollary 3 (`cor:semisimple`, line 340), the exact defective example (line 361 onward), the divergent-limit example, and the scope and bibliography sections. The full proof was audited, not only the finite certificate.

## Independent proof audit

### Assumptions, Stein identity, and pencil: PASS

The theorem assumes that the complex symmetric stabilizing solutions exist for eta>0, that H_eta=Im X_eta is positive definite, that S_eta=X_eta inverse A has spectral radius less than one, and that X_eta tends to a finite invertible X. The conclusion is conditional on these assumptions. In particular it does not establish a finite nonsingular limit for every real A,Q.

Taking imaginary parts of the Riccati equation and using Im(X_eta inverse)=-X_eta inverse adjoint H_eta X_eta inverse gives

\[
H_\eta-S_\eta^*H_\eta S_\eta=\eta I.
\]

The polynomial factorization

\[
P_\eta(\lambda)=(I-\lambda S_\eta^T)X_\eta(S_\eta-\lambda I)
\]

is correct: X_eta S_eta=A, S_eta transpose X_eta=A transpose, and X_eta+S_eta transpose X_eta S_eta=Q+i eta I. Its determinant is not the zero polynomial when X_eta is invertible, including at the limit. Zero and infinite eigenvalues from singular A are not excluded incorrectly; the stable factor has n finite eigenvalues, while reciprocal eigenvalues of the other factor lie outside the unit disk on the extended plane.

The pencil with M_eta=[[A,0],[Q+i eta I,-I]] and L=[[0,I],[A transpose,0]] is a regular linearization. Its stable graph is [I;X_eta], and the lifted eigenvector [v;(Q+i eta I-lambda A transpose)v] has pencil residual [P_eta(lambda)v;0]. For stable eigenvectors of S_eta, the Stein identity yields exactly the stated kernel eta v_a* v_b/(1-conjugate(lambda_a)lambda_b).

### Rellich branches and stable-root counts: PASS

At a unit-circle point e to the i theta_0, the local analytic Hermitian family is

\[
T(t)=e^{i(\theta_0+t)}A^T+e^{-i(\theta_0+t)}A-Q.
\]

Local real-analytic unitary diagonalization and holomorphic continuation suffice; a global periodic analytic eigenbasis is not assumed. The reflected identity U(conjugate(t))* U(t)=I is valid by analytic continuation. Analytic equivalence and the locally invertible change of spectral variable identify each positive order ell_j in d_j(t)=a_j t to the ell_j+... with a unit-circle partial multiplicity. Regularity excludes an identically zero local branch.

The scalar perturbation subtracts i eta I and leaves the same local eigenvectors. For each branch, d_j(t)=i eta has ell_j distinct small roots t_a=epsilon z_a+O(epsilon squared), where epsilon=eta to the 1/ell_j and a_j z_a to the ell_j=i. None of the limiting roots is real. Stability is equivalent to Im t>0. Counting roots in the upper half-plane gives ell/2 for even ell, (ell+1)/2 for positive leading coefficient and odd ell, and (ell-1)/2 for negative leading coefficient and odd ell. Coincidences of roots from different branches cause no difficulty because the corresponding columns of U remain independent.

### Confluent interpolation and complete stable basis: PASS

The interpolation lemma applies to analytic vector columns f(t_a). Multiplication of their sample matrix by the inverse transpose of the Vandermonde matrix gives coefficients of the interpolating polynomial, which tend to the first r Taylor coefficients as all r distinct nodes approach zero. The divided-difference contour formula gives uniform bounds; conversion from Newton to monomial coefficients preserves the required convergence. Applying this separately in two variables also bounds transformed holomorphic kernels, including different node scales. The lifted vectors' eta dependence is uniformly holomorphic on the local contour and does not invalidate this argument.

For each branch, the limiting lifted columns are the prefix of a canonical pencil Jordan chain, of length equal to its stable-root count. The analytic diagonalization supplies a full canonical system of root functions; its associated full lifted chains are independent, and hence their selected prefixes are independent. The change from t to lambda only performs invertible triangular changes within chains. Strictly interior eigenvalues admit an analytic invariant-subspace basis from a fixed resolvent spectral projector, including defective interior eigenvalues. A shift (M_eta-sigma L) inverse L permits this construction even when L is singular.

These columns combine to a full-rank limiting stable basis W_0 of n columns. Write W_eta=[B_eta;C_eta]. Since the stable space is the graph of X_eta, C_eta=X_eta B_eta. The finite-limit assumption gives C_0=XB_0. Full column rank of W_0 now forces B_0 to be invertible. This is the critical step that makes the ensuing Gram limit a valid computation of rank H, despite the ill conditioning of the original eigenvector/Vandermonde bases. It is not enough merely to count the stable roots, and the source does not make that shortcut.

### Every limiting Gram block: PASS

On the strictly stable invariant subspace, the restricted Stein operator has a uniformly bounded inverse as eta tends to zero. Its Gram block is O(eta). Positivity and the Cauchy–Schwarz inequality then force cross terms with all bounded limiting blocks to vanish.

For two branches at the same circle point, writing u_i(s)=v_i(conjugate(s))* gives the holomorphic identity

\[
u_i(s)v_j(t)=\delta_{ij}+(t-s)F_{ij}(s,t).
\]

The denominator 1-exp(i(t-s)) has a simple zero along t=s. For different branches, the numerator has the same factor and the quotient extends holomorphically. After multiplication by eta and interpolation on both sides, these mixed blocks tend to zero, even when the branches have different orders and node scales. For different circle points the denominator is already nonzero locally. For one branch, the holomorphic remainder again vanishes after transformation, leaving only the universal scalar kernel.

For that kernel, with epsilon=eta to the 1/ell,

\[
K=\epsilon^{\ell-1}(C+O(\epsilon)),\qquad
C_{ab}=\frac{i}{z_b-\overline{z_a}}.
\]

C is strictly positive definite: it is the L2 Gram matrix of distinct exponential functions exp(i z_a u) on u>=0, whose imaginary parts are positive. Factoring the Vandermonde as a bounded limiting Vandermonde times diag(1,epsilon,...,epsilon to the r-1) gives transformed entries with exponents ell-1-k-l, 0<=k,l<r. The smallest exponent is ell+1-2r. It equals 1 for even ell, 0 for positive odd ell, and 2 for negative odd ell. Thus no error term is amplified to an uncontrolled limit. Precisely in the positive-odd case, the last diagonal entry has exponent zero and positive limiting coefficient; all other entries vanish. A branch with no selected stable root contributes no column.

The block therefore contributes rank one for a positive odd branch and rank zero otherwise. The mixed blocks vanish and the limiting upper basis B_0 is invertible, so rank H is exactly the number of positive odd branches. This establishes the signed count before the real-symmetry argument.

### Reality, endpoints, inverse rank, and semisimple corollary: PASS

Real A,Q give T(-theta)=conjugate(T(theta))=T(theta) transpose. The multiset of analytic eigenvalue germs at theta and -theta is paired under t to -t. Consequently odd-order leading coefficients occur with opposite signs, while their orders are unchanged. At theta=0 and theta=pi this is a pairing inside the same local germ collection, using periodicity at pi; no exceptional unpaired endpoint branch is possible. Thus the total number of odd blocks is even and half have positive leading coefficient.

Theorem 1 follows: rank(Im X)=b_odd/2. Invertible congruence in Im(X inverse)=-X inverse adjoint H X inverse proves equal rank for the inverse, without asserting that its imaginary part is positive. Since H is positive semidefinite, H=0 is equivalent to the absence of odd blocks.

In the semisimple case every local order is one. The selected roots and eigenvectors are analytic in eta and converge with O(eta) error; the strictly interior invariant basis is analytic as well. Therefore W_eta=W_0+O(eta). Invertibility of B_0 gives X_eta-X=O(eta), and then S_eta-S=O(eta). The rank formula reduces to half the total number of unit-circle eigenvalues. The proof establishes this without separately assuming the O(eta) regularity or same-direction splitting condition used in the cited earlier semisimple theorem. It remains a real-case corollary.

### Exact defective example and selection of the limit: PASS

For the displayed 3 by 3 A,Q, direct expansion gives det P(lambda)=(lambda-1) to the sixth divided by four. Independently, the nonzero entries relevant to this determinant are P_11=-(lambda-1) squared and P_23=P_32=-(lambda-1) squared/2, while P_12=P_21=P_22=0. Their determinant contribution is -P_11 P_23 P_32, confirming the polynomial identity without a numerical root computation.

The Schur complement of the final pivot of T(theta) is

\[
\begin{pmatrix}
(1-\cos\theta)^2&-i\sin\theta(1-\cos\theta)\\
i\sin\theta(1-\cos\theta)&-(1-\cos\theta)^2
\end{pmatrix}
=\frac{\theta^3}{2}\begin{pmatrix}0&-i\\i&0\end{pmatrix}+O(\theta^4).
\]

The spectral mass in the eigenvalue-dependent Schur complement tends to the identity, so the two small Rellich branches have leading terms plus and minus theta cubed/2. This identifies two partial multiplicities of size three, not just total algebraic multiplicity six.

For the displayed X, direct column multiplication verifies XS=A with S=[[1,0,1],[0,1,i],[0,0,1]], and X+A transpose S=Q. Also det X=det A=1/4 and Im X=diag(0,0,1/2), of rank one. The last row of S is the last coordinate row, confirming S*H S=H.

Checking a Riccati residual alone would not identify the limiting stabilizing solution. The source supplies a valid graph selection argument. The positive branch starts at v_+=(1,i,0) and has derivative with third coordinate i; the negative branch starts at v_-=(1,-i,0). Stable selection takes two columns from the positive branch and one from the negative branch. Their upper confluent columns are independent: modulo the first two coordinate directions, the derivative is (0,0,i). The corresponding lower lifted derivative is (Q-A transpose)v'_+ - i A transpose v_+. These data determine the displayed X and give an invertible upper limiting block before assuming this example has a finite limit. Hence the selected stable graph really tends to X; the example is not a circular application of the conditional main theorem.

The final divergent example also checks: A=[[0,1],[0,0]], Q=0, X_eta=diag(i eta,i(eta+eta inverse)) solves the equation, has positive imaginary part and nilpotent S_eta, but diverges. Its limiting polynomial has determinant -lambda squared and no circle roots. This correctly demonstrates that finite-limit existence is an additional hypothesis, not a consequence of circle eigenvalue counting alone.

## Primary-source comparison

Primary sources accessed on 2026-09-11:

- [Guo, Kuo, and Lin, author preprint of the SIAM paper](https://uregina.ca/~chguo/simax81470.pdf): Theorem 2.2 and the adjacent stabilizing characterization support the real regularized solution setting. Theorem 3.3 gives the rank bound and equality under the stated semisimple regularity or splitting hypotheses. The supplied manuscript's corollary addresses these auxiliary restrictions; the simple real case itself was already available.
- [Guo, Kuo, and Lin, author preprint of the JCAM paper](https://uregina.ca/~chguo/JCAM_GuoKuoLin.pdf): Theorem 5 and the following conjecture concern the general complex formulation reflected in canonical MF-18. The rank upper bound is established there and the simple-circle equality is conjectured. This source confirms the substantive scope difference between the submitted real model and the canonical problem.
- [Barbarino and Noferini, arXiv:2211.15539](https://arxiv.org/pdf/2211.15539): Theorem 1.1 states the local analytic Hermitian diagonalization used here; Section 5 relates branch vanishing orders and signs to partial multiplicities and sign characteristics. The manuscript uses this local machinery rather than assuming a global periodic Rellich basis.

The audit verifies these dependencies and their relevant scopes. It does not establish first discovery of the parity theorem or its corollary, and it does not infer an author's identity from file provenance.

## Computations and their limits

The supplied standard-library exact-arithmetic program `code/nano_rank_certificate.py` was read and rerun with `--verify`. It passed. It checks the example over rational complex arithmetic, including the Riccati identity, determinants, imaginary part, graph data, and ranks 4,2,0 of powers of the shifted 6 by 6 linearization, which identify two Jordan blocks of size three. The stored certificate is consistent with that rerun.

The independent determinant, Schur-complement, matrix-product, and stable-graph calculations above supplement that code. Neither the program nor a finite example proves the universal parity theorem; the universal verdict rests on the analytic proof audit, including its confluent and cross-branch limiting steps.

No substantive gap was found in the stated real-case theorem. Its finite invertible limit, real coefficients, symmetry, scalar regularization, and stabilizing-solution assumptions must remain explicit. The manuscript supplies an auxiliary result relevant to MF-18, while the general complex canonical simple-circle conjecture remains unresolved by this submission.
