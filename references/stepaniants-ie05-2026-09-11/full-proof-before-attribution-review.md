# An order-eight counterexample to the orthogonal partial-pivoting extremizer conjecture

**George Stepaniants**  
Department of Computing and Mathematical Sciences  
California Institute of Technology, Pasadena, California, USA  
11 September 2026

## Theorem

Let $L_8$ be the unit lower triangular matrix with every entry below the diagonal equal to $-1$, and let $Q_8$ be its orthogonal factor in the QR factorization with positive diagonal in the triangular factor. There is an explicit real orthogonal matrix $\widetilde Q\in O(8)$ for which partial pivoting, choosing the first available row in every tie, gives

$$
\rho_{\mathrm{PP}}(\widetilde Q)=\frac{5272}{63}
>\sqrt{\frac{17948132}{2601}}
=\rho_{\mathrm{PP}}(Q_8).
$$

In particular, the equality proposed in IE-05 is false. The supremum over all orthogonal matrices and admissible partial-pivoting paths is strictly greater than the proposed value already at order eight.

All computations below are in exact arithmetic. The proof supplies integer matrices, rational squared norms and exact pivot paths. Decimal approximations are unnecessary for the comparison.

## 1. The matrix and its QR convention

Put

$$
\widetilde L=L_8+e_8e_2^T.
$$

Thus the only modification is that the entry in row $8$, column $2$ is changed from $-1$ to $0$. Define

$$
H=
\begin{pmatrix}
 1&-1&-3&-21&-41&-101&-325&63\\
-1& 3& 1& 17& 71& 291&1179&31\\
-1&-1&13&-19&-56&-196&-752&16\\
-1&-1&-3&189&-28&-98&-376&8\\
-1&-1&-3&-51&581&-49&-188&4\\
-1&-1&-3&-51&-213&1507&-94&2\\
-1&-1&-3&-51&-213&-873&2589&1\\
-1& 1&-5&-55&-183&-683&-2683&1
\end{pmatrix}
$$

and

$$
D=\operatorname{diag}(8,16,240,47640,472430,3644970,16148136,5272).
$$

Direct integer multiplication gives

$$
H^TH=D.
$$

Consequently

$$
\widetilde Q=HD^{-1/2}
$$

is exactly orthogonal. To identify its QR convention and elimination multipliers, define the upper triangular matrix

$$
T=
\begin{pmatrix}
1&-1&-3&-21&-41&-101&-325&63\\
0&2&-2&-4&30&190&854&94\\
0&0&8&-44&-67&-107&-223&173\\
0&0&0&120&-106&-116&-70&338\\
0&0&0&0&397&-183&48&672\\
0&0&0&0&0&1190&190&1342\\
0&0&0&0&0&0&3063&2683\\
0&0&0&0&0&0&0&5272
\end{pmatrix}.
$$

Another direct integer multiplication gives

$$
H=\widetilde L T.
$$

Therefore

$$
\widetilde L=\widetilde Q\,(D^{1/2}T^{-1}).
$$

The second factor is upper triangular with positive diagonal, so $\widetilde Q$ is precisely the orthogonal factor in the specified positive-diagonal QR factorization of $\widetilde L$.

## 2. An admissible partial-pivoting path

The factorization

$$
\widetilde Q=\widetilde L\,(TD^{-1/2})
$$

is its no-exchange LU factorization, with positive nonzero diagonal in the upper factor. After eliminating columns $1,\ldots,k-1$, the active first-column entries are

$$
(\widetilde S_k)_{i,k}
=\widetilde L_{i,k}\,(TD^{-1/2})_{k,k},
\qquad i=k,\ldots,8.
$$

Because $\widetilde L_{k,k}=1$ and every strict-lower entry of $\widetilde L$ is $-1$ or $0$, the diagonal entry is a largest-magnitude entry in the active first column. It is also its first available row. Thus the stipulated tie rule makes no row exchanges at any step. The elimination multipliers are exactly the strict-lower entries of $\widetilde L$.

More explicitly, if $I_k=\{k,k+1,\ldots,8\}$, then the active Schur complement is

$$
\widetilde S_k
=\widetilde L_{I_k,I_k}T_{I_k,I_k}D_{I_k,I_k}^{-1/2}.
$$

This formula reduces every squared entry comparison to rational arithmetic.

## 3. Exact growth of the counterexample

The largest absolute entries of the eight columns of $H$ are, respectively,

$$
(1,3,13,189,581,1507,2683,63).
$$

Dividing their squares by the corresponding diagonal entries of $D$ shows that the largest squared entry of $\widetilde Q$ is

$$
\|\widetilde Q\|_{\max}^2=\frac{63^2}{5272}.
$$

Using the Schur-complement formula from Section 2 gives the following exact table. Each entry in its second column is $\sqrt{5272}\,\|\widetilde S_k\|_{\max}$; the third column identifies an entry attaining the maximum in the original row and column numbering.

| Stage $k$ | $\sqrt{5272}\,\|\widetilde S_k\|_{\max}$ | Location |
|---|---:|---|
| 1 | $63$ | $(1,8)$ |
| 2 | $94$ | $(2,8)$ |
| 3 | $173$ | $(3,8)$ |
| 4 | $338$ | $(4,8)$ |
| 5 | $672$ | $(5,8)$ |
| 6 | $1342$ | $(6,8)$ |
| 7 | $2683$ | $(7,8)$ |
| 8 | $5272$ | $(8,8)$ |

These values can be verified directly from the displayed integer matrices: form $\widetilde L_{I_k,I_k}T_{I_k,I_k}$, square each entry in column $j$, and divide by $D_{jj}$. In particular the maximum over all stages occurs at the final pivot and equals $\sqrt{5272}$. Hence

$$
\rho_{\mathrm{PP}}(\widetilde Q)
=\frac{\sqrt{5272}}{63/\sqrt{5272}}
=\frac{5272}{63}.
$$

## 4. Exact comparison with the specified candidate

For completeness, the candidate $Q_8$ also has an integer-column description:

$$
H_0=
\begin{pmatrix}
1&-5&-8&-12&-16&-16&0&64\\
-1&13&-4&-6&-8&-8&0&32\\
-1&-3&51&-3&-4&-4&0&16\\
-1&-3&-11&169&-2&-2&0&8\\
-1&-3&-11&-43&511&-1&0&4\\
-1&-3&-11&-43&-171&1365&0&2\\
-1&-3&-11&-43&-171&-683&1&1\\
-1&-3&-11&-43&-171&-683&-1&1
\end{pmatrix},
$$

$$
D_0=\operatorname{diag}(8,248,3286,36146,349184,2796544,2,5462).
$$

Direct multiplication gives $H_0^TH_0=D_0$, while $T_0=L_8^{-1}H_0$ is upper triangular with positive diagonal

$$
(1,8,31,106,341,1024,1,5462).
$$

Thus $Q_8=H_0D_0^{-1/2}$ has exactly the prescribed QR convention. Its no-exchange path is again the partial-pivoting path with the first available row chosen in a tie.

The largest absolute entries of the columns of $H_0$ are

$$
(1,13,51,169,511,1365,1,64),
$$

so exact squared comparisons give

$$
\|Q_8\|_{\max}^2=\frac{51^2}{3286},
$$

attained at $(3,3)$. The corresponding active maxima are

| Stage $k$ | $\|S_k^{(0)}\|_{\max}$ |
|---|---|
| 1 | $51/\sqrt{3286}$ |
| 2 | $96/\sqrt{5462}$ |
| 3 | $176/\sqrt{5462}$ |
| 4 | $344/\sqrt{5462}$ |
| 5 | $684/\sqrt{5462}$ |
| 6 | $1366/\sqrt{5462}$ |
| 7 | $2731/\sqrt{5462}$ |
| 8 | $5462/\sqrt{5462}$ |

The table follows either by direct no-exchange elimination of $H_0$ with the fixed positive column scalings, or by

$$
S_k^{(0)}=(L_8)_{I_k,I_k}(T_0)_{I_k,I_k}(D_0)_{I_k,I_k}^{-1/2}.
$$

Therefore

$$
\rho_{\mathrm{PP}}(Q_8)^2
=\frac{5462\cdot3286}{2601}
=\frac{17948132}{2601}.
$$

Finally, the squared growth factors differ by the strictly positive rational number

$$
\left(\frac{5272}{63}\right)^2
-\frac{17948132}{2601}
=\frac{117335164}{1147041}>0.
$$

Both growth factors are positive, so the claimed strict inequality follows. This proves the theorem. $\square$

## Scope and attribution

This counterexample refutes the exact extremizer equality asked in IE-05. It does not determine the true orthogonal supremum in dimension eight or in general, and it does not refute a separate assertion about the asymptotic exponential rate or its leading constant.

The proposed family and its original growth analysis are due to John Peca-Medlin, [*Growth factors of orthogonal matrices and local behavior of Gaussian elimination with partial and complete pivoting*, arXiv:2308.16146v2](https://arxiv.org/html/2308.16146v2), Section 3.2 and Appendix B; published in [SIAM Journal on Matrix Analysis and Applications 45 (2024), 1599–1620](https://doi.org/10.1137/23M1597733). The proof above is self-contained: it does not invoke the paper's extremal assertions to certify either growth factor.
