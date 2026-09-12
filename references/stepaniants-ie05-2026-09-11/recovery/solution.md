---
title: "An order-eight counterexample to the orthogonal GEPP extremizer in IE-05"
subtitle: "Exact negative resolution of the displayed finite-dimensional equality"
date: "September 2026"
---

# Target and result

The repository's IE-05 asks whether the positive-diagonal QR factor $Q_n$ of the unit lower triangular matrix $L_n$ with all strict lower entries $-1$ maximizes partial-pivoting element growth over $O(n)$, for every $n\geq2$ [1]. The candidate uses first-available-row tie breaking; the supremum permits every admissible path. All arithmetic below is exact. Write

$$
\rho_{\rm PP}(A)=\frac{\max_{1\leq k\leq n}\|S_k(A)\|_{\max}}
{\|A\|_{\max}},
$$

where $S_k$ is the active Schur complement before pivot $k$.

**Theorem.** Set $L_0=L_8$ and

$$
L_* = L_8+e_7e_2^T.
$$

Thus only entry $(7,2)$ is changed, from $-1$ to $0$, using one-based indices. Let $Q_*$ be the orthogonal factor in $L_*=Q_*R_*$ with positive diagonal in $R_*$. With first-available-row tie breaking,

$$
\rho_{\rm PP}(Q_*)=\frac{5272}{63}
>\frac{\sqrt{17948132}}{51}=\rho_{\rm PP}(Q_8).
\tag{1}
$$

Consequently, the universal equality in IE-05 is false already at $n=8$.

# QR factors and the admissible pivot path

For any real unit lower triangular $L$ whose strict lower entries have absolute value at most one, take its positive-diagonal QR factorization $L=QR$. Then $Q=LU$ with $U=R^{-1}$ upper triangular and positive on the diagonal. After $k-1$ no-swap elimination steps, the active matrix is

$$
S_k(Q)=L_{k:n,k:n}U_{k:n,k:n}.
\tag{2}
$$

Its first column has entries $U_{kk}$ in its first row and $L_{ik}U_{kk}$ below. The first entry therefore has largest absolute value, and first-available-row tie breaking selects it. Induction proves that no row exchanges occur. This applies to both $L_0$ and $L_*$, including their exact ties. In particular, the counterexample is not a rounding-induced pivot-path artifact.

For an explicit radical representation, define the following integer-column matrices:

$$
M_0=\begin{pmatrix}
1&-5&-8&-12&-16&-16&0&64\\
-1&13&-4&-6&-8&-8&0&32\\
-1&-3&51&-3&-4&-4&0&16\\
-1&-3&-11&169&-2&-2&0&8\\
-1&-3&-11&-43&511&-1&0&4\\
-1&-3&-11&-43&-171&1365&0&2\\
-1&-3&-11&-43&-171&-683&1&1\\
-1&-3&-11&-43&-171&-683&-1&1
\end{pmatrix},
\tag{3}
$$

$$
M_*=\begin{pmatrix}
1&-1&-3&-21&-41&-101&325&63\\
-1&3&1&17&71&291&-1179&31\\
-1&-1&13&-19&-56&-196&752&16\\
-1&-1&-3&189&-28&-98&376&8\\
-1&-1&-3&-51&581&-49&188&4\\
-1&-1&-3&-51&-213&1507&94&2\\
-1&1&-5&-55&-183&-683&2683&1\\
-1&-1&-3&-51&-213&-873&-2589&1
\end{pmatrix}.
\tag{4}
$$

Direct integer dot products give $M_a^TM_a=\operatorname{diag}(s_a)$, for $a\in\{0,*\}$, where

$$
\begin{aligned}
s_0&=(8,248,3286,36146,349184,2796544,2,5462),\\
s_*&=(8,16,240,47640,472430,3644970,16148136,5272).
\end{aligned}
\tag{5}
$$

Furthermore, $T_a=L_a^{-1}M_a$ is upper triangular, with positive diagonal

$$
\begin{aligned}
\operatorname{diag}(T_0)&=(1,8,31,106,341,1024,1,5462),\\
\operatorname{diag}(T_*)&=(1,2,8,120,397,1190,3063,5272).
\end{aligned}
\tag{6}
$$

These claims are finite rational identities: $T_a$ can be checked by the row recurrence

$$
(T_a)_{ij}=(M_a)_{ij}-\sum_{h<i}(L_a)_{ih}(T_a)_{hj}.
\tag{7}
$$

Equations (5)--(6) imply that

$$
Q_a=M_a\operatorname{diag}(s_a)^{-1/2}
\tag{8}
$$

is orthogonal and is precisely the positive-diagonal QR factor of $L_a$: indeed $Q_a=L_aU_a$, where $U_a=T_a\operatorname{diag}(s_a)^{-1/2}$ is upper triangular with positive diagonal, so $L_a=Q_aU_a^{-1}$. All square roots in (8) are positive. In particular, $Q_0=Q_8$ as specified by the repository, not a numerically approximated substitute.

# Exact growth certificate

The diagonal column normalization in (8) commutes with the no-swap elimination updates: carry out rational elimination on $M_a$, and divide column $j$ of each active matrix by $\sqrt{(s_a)_j}$. Thus every squared entry magnitude is rational. At step $k$, with rational work matrix $H$, update

$$
H_{ij}\ \longleftarrow\ H_{ij}-\frac{H_{ik}}{H_{kk}}H_{kj},
\qquad i,j>k.
\tag{9}
$$

The following table lists **all** squared active-stage maxima, including the input stage. It follows by (3)--(5) and (9); no approximate comparison is involved.

| Stage $k$ | $\|S_k(Q_8)\|_{\max}^2$ | $\|S_k(Q_*)\|_{\max}^2$ |
|:---:|---:|---:|
| 1 | $2601/3286$ | $3969/5272$ |
| 2 | $4608/2731$ | $2209/1318$ |
| 3 | $15488/2731$ | $29929/5272$ |
| 4 | $59168/2731$ | $28561/1318$ |
| 5 | $233928/2731$ | $56448/659$ |
| 6 | $932978/2731$ | $450241/1318$ |
| 7 | $2731/2$ | $7198489/5272$ |
| 8 | $5462$ | $5272$ |

The input maxima occur at $(3,3)$ for $Q_8$ and $(1,8)$ for $Q_*$. The final stage is largest in each column of the table. Therefore

$$
\rho_{\rm PP}(Q_8)^2=\frac{5462}{2601/3286}
=\frac{17948132}{2601},
\qquad
\rho_{\rm PP}(Q_*)^2=\frac{5272}{3969/5272}
=\frac{27793984}{3969}.
\tag{10}
$$

The strict comparison reduces to the positive integer

$$
27793984\cdot2601-17948132\cdot3969=1056016476>0.
\tag{11}
$$

Taking positive square roots proves (1). Since $Q_*\in O(8)$ and its demonstrated path is admissible, its growth is a lower bound for the supremum in IE-05. This completes the disproof.

For orientation only, the two growth factors are approximately $83.06908970234$ and $83.68253968254$. The proof does not use these decimals.

\newpage

# Scope and reproducibility

This resolves the displayed yes-or-no statement negatively. It does **not** determine the true supremum at $n=8$, identify a globally optimal replacement family, or resolve the asymptotic optimal constant discussed in [2]. It also does not claim that eight is the smallest failing dimension. The distinction between a large generated entry and a large *normalized* growth factor matters: the counterexample has a smaller largest generated entry but a sufficiently smaller input maximum.

`verify_exact.py` reconstructs both matrices by rational Gram--Schmidt and verifies the full certificate. `independent_check.py` instead begins with the explicit integer columns and reconstructs every Schur complement using a leading-block inverse. This is a second implementation, not independent human or external-agent review. Both use only Python's standard library.

```text
python verify_exact.py
python independent_check.py
```

The package includes `certificate.json` and successful verification transcripts. This manuscript is an AI-assisted, reconstructed proof submission for review, not a claim of established publication, formal proof-assistant certification, or priority.

# References

[1] OpenProblemsInNLA, IE-05, canonical statement, problem statement and pivot-path conventions; accessed during the recovery session. [Repository entry](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/linear-systems-and-elimination/IE-05).

[2] J. Peca-Medlin, *Growth factors of orthogonal matrices and local behavior of Gaussian elimination with partial and complete pivoting*, SIAM Journal on Matrix Analysis and Applications 45 (2024), 1599--1620. Section 3.2 and Appendix B. [Author manuscript, version 2](https://arxiv.org/html/2308.16146v2). DOI: 10.1137/23M1597733.
