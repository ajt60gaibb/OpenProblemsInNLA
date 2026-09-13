# Proof audit for MI-27

This is an explicit internal audit, not an external referee report. The core result is a proved universal inequality using one published non-elementary identity. Numerical consistency tests are supplementary only.

## 1. Exact target and norm convention

The theorem is stated for every finite dimension and arbitrary complex positive definite A and B with tr(A+B)=1. The norm is the full Schatten 1-norm, not the half-normalized trace distance. Logarithms are natural. The coefficient on binary entropy is exactly 1.

## 2. The external identity is genuinely noncommutative

The imported formula is Hirche–Tomamichel, Corollary 2.3, equation (2.22), derived from Frenkel, Theorem 6. It represents Umegaki relative entropy itself, not a classical surrogate or an alternative quantum f-divergence. The formula was checked in both the HTML and rendered PDF of arXiv:2306.12343v3, PDF page 7. The trace correction appearing for unnormalized matrices in Frenkel's version is zero because both inputs here are states of trace one.

## 3. No erroneous factor two in the elementary lemma

For any effect Q, 2Q-I is a contraction, and [X,Q]=[X,2Q-I]/2. Thus the two trace-norm product bounds are exactly canceled by this factor 1/2. For a density matrix X the result is ||[X,Q]||_1 <= 1. A pure qubit state and a rank-one projection attain equality.

## 4. The optimal projection commutes with the whole pencil

The chosen Q_t is the spectral projection of rho-gamma sigma_t. Hence [rho,Q_t]=gamma[sigma_t,Q_t], with precisely the factor needed to eliminate gamma from the unitary derivative. No commutativity of rho and sigma is assumed.

## 5. Zero eigenvalues and eigenvalue crossings

No derivative of Q_t is used. The scalar positive-part trace is Lipschitz in the trace norm, so its composition with the smooth matrix path is locally Lipschitz. At any differentiability point, keeping Q_t fixed in the variational formula and taking positive and negative time increments proves the derivative formula. Absolute continuity then integrates the almost-everywhere derivative bound. Persistent kernels and isolated or nonisolated zero crossings do not invalidate the argument.

## 6. Both orientations are controlled

The proof directly controls E_gamma(rho || U_t sigma U_t*). Joint unitary invariance converts E_gamma(U_t sigma U_t* || rho) into the same problem with generator -H. Its operator norm is unchanged. Therefore both integrands in the entropy representation have the same constant 1.

## 7. The change-of-variable factors are exact

For M=alpha rho+beta sigma, the first integral stops at v=1/alpha. The changes of variables are v=gamma/(beta+alpha gamma) and v=alpha+beta gamma. Their Jacobians produce the squared denominators in the skew-divergence kernels. Nine exact symbolic checks include these kernel primitives, the two coefficient combinations, and the sharpness-family determinant identities.

## 8. Positivity and mass of the final kernels

After adding the two weighted skew relative entropies, the coefficients are ab/[gamma(b+a gamma)] and ab/[gamma(a+b gamma)]. They are nonnegative for a,b>0, and their masses are -a log a and -b log b. The positive-part divergence lies between 0 and 1 for gamma>=1. All relevant derived integrals are therefore finite.

## 9. No unjustified derivative–integral interchange

The finite-time positive-part Lipschitz bounds are integrated first. Only after obtaining the scalar entropy finite-difference bound is the smooth entropy path differentiated at zero. Thus no uniform control of derivatives of moving spectral projections and no differentiation under an improper integral are required.

## 10. Entropy derivative and dual witness

With T_t=A+exp(itH)B exp(-itH), T'_0=i[H,B] has trace zero. The entropy derivative is -i tr H[B,log(A+B)]. Therefore K=-i[B,log(A+B)] is the relevant Hermitian matrix. Choosing H=sign(K) is legitimate: it is Hermitian, has operator norm at most 1, and gives tr HK=||K||_1=||[B,log(A+B)]||_1. The numerical suite separately checks this sign and normalization.

## 11. Strictness and the lower bound on the optimal coefficient

In the pack's family the congruence middle factor has eigenvalues t^2 and 1-t^2. Both A_t and B_t are strictly positive definite for every 0<t<1/2; no semidefinite boundary point is substituted into the original theorem. The commutator norm and binary entropy both have leading term 2t log(1/t), so their ratio tends to 1. This establishes optimality analytically, not merely numerically.

## 12. Arbitrary rank and the pack's remaining gap

The upper-bound argument never reduces to rank-one states or projections. It applies directly to arbitrary states in every finite dimension. The projection inequality is a consequence by regularization. The converse equivalence from the pack uses a convex combination with varying trace values and concavity of binary entropy; it does not incorrectly assert that fixed-trace extreme points are always projections.

## 13. Numerical scope and limitations

The final verification script uses deterministic samples, generalized-eigenvalue breakpoints for quadrature, stable binary entropy, and precision increasing with the sharpness parameter. The largest observed error among 60 matrix integral evaluations was approximately 1.07e-14. Finite sampling is not evidence sufficient to prove a universal matrix inequality and is not used that way in the write-up. In preliminary exploration, unstable evaluation of 1-b near endpoints produced spurious ratios; none of those unstable exploratory values is included in the verification results or relied on by the proof.

## Dependency conclusion

The proof depends on finite-dimensional spectral calculus, the trace-norm product inequality and duality, elementary real-variable facts about Lipschitz functions, and the cited published relative-entropy representation. The stated MI-27 upper bound, and the sharpness of its universal coefficient, have no remaining unproved auxiliary claims in this write-up. This audit is internal; independent mathematical review and formal verification have not been performed.
