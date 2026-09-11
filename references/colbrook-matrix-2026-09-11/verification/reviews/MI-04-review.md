# MI-04 independent proof review

**Verdict: PASS — full canonical target proved.** No material mathematical gap found. This is a direct mathematical review, not formal proof-assistant verification or a claim of publication priority.

Reviewed 2026-09-11. Original: `.cache/colbrook-matrix-submission/nla_submission/proofs/MI-04.tex`. SHA256 of the complete original decoded as UTF-8, replacing CRLF by LF, with no trimming: `8363d460f59fba544577ba6453e44cec51f9b546a01875515361df352321fb7c`.

## Exact target and conventions

The canonical `matrix-inequalities-and-norms/MI-04/README.md` asks whether the operator-norm inequality for every positive semidefinite completion with a fixed off-diagonal block X forces X to be essentially Hermitian, in every finite dimension. The manuscript proves precisely this necessity, and also its converse and two equivalent intermediate conditions. The preamble defines the manuscript's infinity-norm notation as the operator norm; it is the canonical README's 2-norm, not its Schatten/Frobenius convention.

The target matches [Bourin–Lee, Conjecture 3.3](https://arxiv.org/html/2111.15180), checked in the primary text on 2026-09-11. The nearby Theorem 3.2 adds invertibility and distinct singular values and concludes normality; Proposition 3.4 concerns the Frobenius norm. Neither is substituted for the target or invoked to supply a missing step. The manuscript supplies its own proof throughout.

## Step-by-step audit

1. **Universal completions to scalar-sum completions:** restriction of the quantifier is immediate. For Hermitian T, K has trace zero, so a=lambda_max(K) and b=-lambda_min(K) are nonnegative. The completion bI+K is positive semidefinite, has norm a+b and diagonal sum 2bI. The assumed norm bound indeed yields a<=b, including b=0. Conjugating -K_X(T) by diag(I,-I) yields K_X(-T), with the off-diagonal block still X. Repeating gives b<=a. If positivity means positive definite, the eta regularization stated in the proof is valid and preserves the limiting conclusion.

2. **Scaling and basis changes:** K_(epsilon X)(T)=epsilon K_X(T/epsilon), for epsilon>0, transfers extreme spectral symmetry. Conjugation by diag(U,U) transfers it under unitary similarity of X, with T ranging over all Hermitian matrices. Thus the basis chosen in the perturbation argument is arbitrary.

3. **Second-order perturbation:** for D=diag(1,d_2,...,d_n), all |d_j|<1, the two extremal eigenvalues of diag(D,-D) are simple and isolated. Other eigenvalues may coincide without affecting this argument. Continuity keeps the two analytic branches extremal for sufficiently small epsilon. The perturbation has zero diagonal blocks, so the linear coefficients vanish. Couplings from the top first basis vector have squared moduli |x_1j|^2 and denominators 1+d_j; couplings from the bottom first basis vector have squared moduli |x_j1|^2 and denominators -(1+d_j). These give exactly the displayed coefficients. The elementary derivation of the simple-eigenvalue coefficient is valid here. One-sided equality for epsilon>0 suffices to equate the quadratic coefficients.

4. **Varying the weights:** the j=1 terms cancel because each is |x_11|^2/2. Holding every d_j except d_l equal to zero and changing d_l to any nonzero value in (-1,1) leaves a nonzero multiplier of |x_1l|^2-|x_l1|^2, forcing it to vanish. Arbitrary bases yield the orthonormal-pair equality. For n=1 this condition is vacuous and the later conclusion is automatically true.

5. **Normality:** completing any unit vector u to an orthonormal basis and summing the pair equalities, with the common diagonal term, proves ||X*u||^2=||Xu||^2. Hence the Hermitian matrix XX*-X*X has zero quadratic form on every unit vector and vanishes. There is no nonsingularity assumption.

6. **Collinearity:** normality provides an orthonormal eigenbasis. The two Fourier vectors associated with any three distinct indices are orthonormal. Their pair condition becomes the equality of the two displayed complex moduli. Direct expansion gives the stated difference 2 sqrt(3) Im(a conjugate(b)), with the stated sign. Its vanishing says the three eigenvalues are collinear. Repeated eigenvalues cause no difficulty. For n<=2 every spectrum is collinear; otherwise any distinct pair determines the common line. A normal matrix with spectrum in an affine line is alpha H+beta I for Hermitian H, by diagonalizing and taking the real coordinates along the line.

7. **Essentially Hermitian to spectral symmetry:** a phase rotation absorbs the phase of alpha, after which X=H+ibI; the scalar case is included. The specified Q is unitary, and its block multiplication gives exactly diagonal blocks -bI,bI and off-diagonal blocks T-iH,T+iH. If T-iH=U Sigma V*, conjugation by diag(U,V) reduces these blocks to scalar 2-by-2 Hermitian blocks. Their eigenvalues are plus/minus sqrt(sigma_j^2+b^2), including zero singular values. Thus the entire spectrum, and in particular its extrema, is symmetric.

8. **Spectral symmetry to all completions:** P>=0 implies A,B>=0. For c=||A+B||, cI-A-B>=0, so adding it to the lower diagonal block gives P'>=P>=0. The decomposition P'=cI/2+K_X(A-cI/2) is exact. Positivity bounds the smallest eigenvalue of K below by -c/2; symmetry bounds the largest above by c/2. Therefore P<=P'<=cI. This proves the required norm bound, including c=0.

## Limitations and disposition

There are no unverified computational certificates, external theorem hypotheses, sharp constants, or omitted dimension cases needed for this proof. The result establishes the canonical necessity without the extra hypotheses of Hayashi's older result. Subject to the repository's normal submission policy, this supports a full affirmative resolution of MI-04. The review does not establish novelty against all literature or replace external peer review. Original proof and canonical files were not edited by this reviewer.
