# IE-17 — Monotonic optimal backward error along LSMR

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** explicit dissertation conjecture; later resolution not located  
**Last checked:** 2026-09-08

Let $A\in\mathbb R^{m\times n}$ and $b\in\mathbb R^m$. In exact arithmetic, start LSMR at $x_0=0$: equivalently, $x_k$ minimizes $\|A^T(b-Ax)\|_2$ over $\mathcal K_k(A^TA,A^Tb)$. Work up to its exact termination and use its minimum-length iterate if necessary. Let $r=b-Ax$ and define the matrix-only normwise backward error
$$
\mu(x)=\min\{\|E\|_2:(A+E)^T((A+E)x-b)=0\}.
$$
For $x\ne0$, put $K_x=[A^T,\,(\|r\|_2/\|x\|_2)I]^T$, $v_x=[r^T,0^T]^T$, and
$$
\widetilde\mu(x)=\frac{\|K_xK_x^{\dagger}v_x\|_2}{\|x\|_2}.
$$
Here $\dagger$ is the Moore–Penrose inverse; at an exact least-squares solution set both errors to zero.

Are both sequences $\mu(x_k)$ and $\widetilde\mu(x_k)$ nonincreasing, for successive nonzero LSMR iterates? These two closely related claims are counted together, as in the source. The right-hand side $b$ is kept fixed in the backward-error model.

A positive answer would justify backward-error stopping decisions without a later iteration making the current iterate less backward accurate. The known monotonicity of $\|r_k\|_2$ and $\|A^Tr_k\|_2$ does not establish this statement.

## References

 D. C.-L. Fong, *Minimum-Residual Methods for Sparse Least-Squares Using Golub–Kahan Bidiagonalization*, Stanford dissertation 2011, §7.2.1 and definitions (4.1),(4.5), printed pp. 56–57,118 ([primary PDF](https://web.stanford.edu/group/SOL/dissertations/david-fong-thesis-online.pdf)). Fong and M. Saunders, *LSMR: An iterative algorithm for sparse least-squares problems*, SISC 33(2011),2950–2971, §§6.1–6.2, Fig7.5 ([author PDF](https://web.stanford.edu/group/SOL/software/lsmr/LSMR-SISC-2011.pdf)). E. Hallman and M. Gu, *LSMB: Minimizing the backward error for least-squares problems*, SIMAX 39(2018),1295–1317 ([author PDF](https://erhallma.math.ncsu.edu/papers/hallman2018lsmb.pdf)).

## Status check — 2026-09-08

 Exact-title and “LSMR optimal backward error monotonicity conjecture/proof/counterexample” searches found no resolution. The LSMB2018 discussion of nonmonotonicity concerns LSQR, and its proposed method differs from LSMR. Hallman's May 2026 arXiv:2605.09211 develops backward-error formulas and estimates, without resolving this iterate-monotonicity conjecture. No recent explicit reaffirmation was located.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
