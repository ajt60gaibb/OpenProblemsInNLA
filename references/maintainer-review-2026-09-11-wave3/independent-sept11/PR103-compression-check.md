# PR #103 — independent compression and constant-loss check

Date: 2026-09-11. Scope: Lemma 2 and the constant-loss assembly in the frozen `pr-103/randomized-and-low-rank-approximation/RA-10/solution.md`, including selected-projector and boundary conventions. This is an independent derivation plus diagnostic computation, not an external peer review or formal verification. I did not inspect or run the submitter’s scripts, modify the snapshot/shared checkout, or perform GitHub actions.

**Verdict: no defect found in the compression lemma or the derivation of constant 11.** The block identities are exact for noncommuting PSD matrices. The passage to singular compressions and the selected zero eigendirections are handled correctly. The numerical checks below corroborate the algebra; they do not prove any universally quantified inequality or establish the optimal constant.

## Independent block derivation

Work in the selected orthogonal decomposition and write

\[
 A=\begin{pmatrix}H&E\\E^T&F\end{pmatrix},\quad
 C=\begin{pmatrix}H&0\\0&0\end{pmatrix},\quad M=sI+H.
\]

For a unit positive eigenvector \(v=(u,w)\) of \(Z=f_s(C)-f_s(A)\), put \(\lambda>0\) and \(\mu=\lambda/(1+\lambda)\). Because \(Z\preceq f_s(C)\prec I\), \(0<\mu<1/2\). Multiplying

\[
 (sI+A)^{-1}v=(sI+C)^{-1}v+(\lambda/s)v
\]

by \(sI+A\), its first block row becomes

\[
 0=\lambda Mu+(1+\lambda)Ew,
\]

so \(Ew=-\mu Mu\). After division by \(1+\lambda\), its second row becomes

\[
 E^T\big((1-\mu)sM^{-1}+\mu I\big)u+(F+\mu sI)w=0.
\]

The bracket equals \((sI+\mu H)M^{-1}\); thus this independently reproduces (2)–(3). It requires only commutation of functions of **the same** \(H\), not commutation of unrelated blocks.

Taking the second row’s inner product with \(w\) and using \(Ew=-\mu Mu\) gives exactly

\[
 w^TFw=\mu s(\|u\|^2-\|w\|^2)+\mu^2u^THu.
\]

For \(H\succ0\), PSD of \(A\) implies \(F\succeq E^TH^{-1}E\). Comparing the resulting lower bound on \(w^TFw\) gives

\[
 \|w\|^2\le(1-2\mu)\|u\|^2-\mu s\,u^TH^{-1}u,
 \qquad \|u\|^2\ge[2(1-\mu)]^{-1}.
\]

Also \(D=C-A\) has blocks \((0,-E;-E^T,-F)\), so direct substitution gives

\[
 v^TDv=-2u^TEw-w^TFw
       =\mu s+\mu(2-\mu)u^THu.
\]

These establish (4)–(6) with their stated signs and constants.

Set \(\Delta=(cI-H)_+\). Substitution of \(H\succeq cI-\Delta\), the bound on \(\|u\|^2\), and \(\lambda=\mu/(1-\mu)\) yields

\[
 v^TDv+\mu(2-\mu)u^T\Delta u
 \ge\frac{\lambda(s+c)}2,
\]

with scalar slack exactly

\[
 \frac{\mu\{s(1-2\mu)+c(1-\mu)\}}{2(1-\mu)}\ge0.
\]

For an orthonormal positive eigenbasis \(v_j\), its compressed components satisfy \(\sum_j u_ju_j^T\preceq I_k\). The varying weights satisfy \(0<\mu_j(2-\mu_j)<1\), so their weighted positive matrices also sum to at most \(I_k\). Consequently the defect penalty sums to at most \(\operatorname{tr}\Delta\). The other term is \(\operatorname{tr}(QD)\le\operatorname{tr}(D_+)\) for the positive spectral projector \(Q\) of \(Z\). This proves the lemma with factor \(2/(s+c)\).

For singular \(H\), \(A+\rho P\succeq0\), its compression is \(C+\rho P\), and their difference is still exactly \(D\). At fixed \(s,c>0\), functional calculus and positive-part traces are continuous as \(\rho\downarrow0\). The proposed limiting argument therefore has no hidden uniform-inverse assumption. If the positive eigenspace is empty, the inequality is immediate.

## Independent constant accounting

For the spectrum-matched \(B_0\), pinching gives

\[
 e_0\ge R+L,\qquad e_C\le e_0+R,\qquad
 e_C=L+2t,\quad t=\operatorname{tr}((C-A)_+),\quad d\le L.
\]

The ridge scalar comparison gives \(L_s\le gL\). Lemma 2 therefore gives the compression excess at most

\[
 gL+4g(t+d)\le g(2e_C+3L).
\]

On the **selected subspace**, the exact resolvent product in (14) obeys the nuclear ideal bound \(gR\). On that subspace \(B_0\succeq cI\); outside it the matrix-function difference is zero. Extending the \(1/(s+c)\) inverse bound to the whole space would be wrong, but the manuscript explicitly does not do so.

Thus the spectrum-matched excess is at most

\[
 g(2e_C+3L+R)
 \le g(2e_0+3R+3L)
 \le5g e_0.
\]

For the original selected \(B\), the ordered-eigenvalue nuclear inequality gives \(r\le e(B)\), including selected zero eigenvalues. The triangle inequality gives \(e_0\le e(B)+r\), and simultaneous diagonalization of \(B,B_0\) gives a ridge difference at most \(gr\). Hence the absolute excess is at most

\[
 5g(e(B)+r)+gr\le11g e(B).
\]

If \(\tau>0\), then \(c=a_k>0\), and every tail eigenvalue is at most \(c\). Thus \(\tau_s\ge g\tau\), giving the claimed relative factor. No positive spectral gap is used.

For \(f(0)=\alpha>0\), functional calculus on the retained rank-\(k\) projector contributes \(\alpha(I-P)\), whose nuclear norm is \(\alpha(n-k)\). The positive linear and ridge combinations preserve the bound; the representation theorem itself is outside this targeted independent check. When \(\tau=0\), the premise forces \(A=B\) exactly and the whole error is \(\alpha(I-P)\), equal to the optimal tail. When \(\varepsilon=0\) and \(\tau>0\), the same excess inequalities force zero transformed excess. Neither argument divides by a vanishing gap or discards a selected zero eigendirection.

## Independent diagnostic calculations

Code: `pr103_compression_check.py`; complete output: `PR103-compression-results.json`, beside this report. The script was written for this review. It uses exact Python fractions, NumPy, and an independently implemented small Decimal Jacobi eigensolver; no submission code or numerical outputs were consumed.

1. **Exact rational algebra:** for \(A=\bigl(\begin{smallmatrix}1&1\\1&1\end{smallmatrix}\bigr)\), \(C=\operatorname{diag}(1,0)\), \(s=1\), the positive eigenvalue of \(Z\) is \(1/3\), with eigenvector proportional to \((-2,1)\) and \(\mu=1/4\). Equations (2), (3), (4), and (6) hold by exact fraction arithmetic. The inverse product in (14) is also checked exactly for the noncommuting active blocks \(B_0=\bigl(\begin{smallmatrix}3&1\\1&3\end{smallmatrix}\bigr)\), \(H=\bigl(\begin{smallmatrix}2&1\\1&1\end{smallmatrix}\bigr)\), \(s=2/3\).
2. **1,800 fixed-seed PSD cases**, sizes 2–8 and every permitted type of selected rank: 1,130 had numerically noncommuting \(B_0,H\), and 600 had rank-deficient selected \(B\). The script checks Lemma 2, the block identities, inequalities (8), (9), (15)–(17), (19)–(20), and transfer for \(f(x)=\alpha+\beta x+x/(s+x)+0.3\sqrt{x}\), with \(\alpha,\beta>0\). No violation exceeded the declared scale-aware floating-point tolerances. The largest scaled block-identity residual was \(2.25\times10^{-15}\). The largest observed lemma LHS/RHS ratio was approximately 0.5000011; the largest observed ridge-excess ratio to \(g e(B)\) was 1.85260, below 11. These are sample observations, not bounds or evidence of optimality.
3. **Seven 145-digit Decimal cases** separately cover a \(10^{-40}\) gap at the truncation threshold, compression eigenvalue \(10^{-70}\), a singular compression, rank-deficient selected \(B\), exact \(\varepsilon=0\) with positive tail, zero tail with \(f(0)>0\) and a selected zero direction, and \(A=B=0\). All applicable checks pass. In the tiny-gap case, \(e(B)=1.28\times10^{-40}\) is resolved numerically. In the nearly singular case, \(\tau\approx5\times10^{-71}\); no instability was used to infer a proof. The singular-compression example with \(\tau=0\) and \(A\ne B\) is tested only for the lemma, since it does not satisfy the transfer premise. The two valid zero-tail cases yield functional error exactly 3 and 6 respectively, matching \((n-k)f(0)\).

The algebra, rather than these diagnostic computations, supports the affirmative verdict. No correction to Lemma 2 or the constant-11 assembly is requested.
