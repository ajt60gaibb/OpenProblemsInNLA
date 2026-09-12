# Supplementary RA-10 audit: eigenvalues and selected functional calculus

Reviewer: separate Codex agent `/root/review_aa01`, 11 September 2026.

This supplements, without modifying, the independent review of the 11,521-byte frozen manuscript `full-proof-candidate.md`, SHA-256 `eaf566e469e1c3a5a21473852c29247d86e7960f87178d0245ea7f89379e8e35`.

**PASS.** Equation (16) applies exactly as written, and no ambiguity in the selected functional calculus changes the theorem's meaning.

## Direct finite-dimensional proof of the eigenvalue estimate

Let X and Y be arbitrary real symmetric or complex Hermitian matrices. Set J=X-Y and write its positive and negative parts as J_+ and J_-, so J=J_+-J_- and ||J||_*=tr J_++tr J_-. Define

    U=X+J_-=Y+J_+.

Then U>=X and U>=Y. If u_i,x_i,y_i denote the respective eigenvalues in decreasing order, min-max gives u_i>=max(x_i,y_i) for every i, including all multiplicities. Hence

    |x_i-y_i| <= 2u_i-x_i-y_i.

Summing gives

    sum_i |x_i-y_i|
      <=2tr U-tr X-tr Y
      =tr J_++tr J_-
      =||X-Y||_*.

For X=A and Y=B=Ahat_k, the ordered eigenvalues of B are b_1,...,b_k followed by n-k zeros, even if some selected b_i are themselves zero. The displayed inequality therefore gives precisely r+tau<=||A-B||_*, and subtracting tau yields r<=e(B). No equality case, strict spectral gap, selected-eigenvector compatibility between A and B, or nonsingularity is used.

## Selected functional calculus

If B=PBP and P is the prescribed rank-k projection, then P commutes with B. For a continuous f on the spectrum,

    f(B)_P=P f(B)P=f(B)-f(0)(I-P).

On range(P) it retains f of every selected eigenvalue, including f(0) when a selected eigenvalue is zero. On ker(P) it is zero by definition. It is therefore exactly f(Ahat)_k in the fixed eigenbasis used to construct B. In contrast, applying f to the full n-dimensional B would retain f(0) on ker(P); the manuscript never makes that incorrect identification.

All intermediate uses of un-subscripted f_s(B), f_s(B0), and f_s(C) are valid because every ridge atom satisfies f_s(0)=0. The integral's constant term contributes alpha(I-P) to the error, while the linear and ridge terms may be written on the full space. Ties in Ahat and ties created by a non-strictly increasing f do not change any argument: the canonical convention fixes the selected eigenvectors before applying f.
