# KE-02: Deterministic separation in a weak-coupling subclass

**Scope:** A complete elementary construction for all dimensions under an
additional small-off-diagonal hypothesis, and an unrestricted order-two
construction. **The original general tridiagonal target remains open here.**
No novelty or independent/formal verification is claimed.

## 1. Statement

Let \(T\in\mathbb C^{n\times n}\) be Hermitian, let \(n\ge2\), and let
\(\delta>0\). Write
\[
T=\operatorname{diag}(t_1,\ldots,t_n)+R,
\quad R_{ii}=0,
\quad\eta=\max_i\sum_{j\ne i}|R_{ij}|.
\]
For a Hermitian matrix, \(\|R\|_2\le\eta\): its eigenvalues lie in the
row-sum Gershgorin intervals, and its spectral norm is its largest absolute
eigenvalue. Equivalently one may use
\(\|R\|_2\le\sqrt{\|R\|_1\|R\|_\infty}=\eta\).

### Theorem 1

There is a deterministic diagonal \(D\), constructible with
\(O(n\log n)\) comparisons and arithmetic operations once the diagonal and
\(\eta\) are available, such that \(\|D\|_2\le\delta\). If
\[
\eta\le\frac{\delta}{2(n-1)},
\tag{1}
\]
then
\[
\operatorname{gap}(T+D)\ge\frac{\delta}{n-1}\ge\frac\delta n.
\tag{2}
\]
For tridiagonal input, computing \(\eta\) also costs \(O(n)\) permitted
operations, so the total is \(O(n\log n)\).

## 2. Construction and proof

Sort the diagonal entries, retaining their original indices:
\(t_{\pi(1)}\le\cdots\le t_{\pi(n)}\). Set
\[
\gamma=\frac{2\delta}{n-1},\qquad
y_1=t_{\pi(1)}-\delta,
\quad y_j=\max\{t_{\pi(j)}-\delta,y_{j-1}+\gamma\}\quad(j\ge2).
\tag{3}
\]
Return the diagonal entries
\[
D_{\pi(j),\pi(j)}=y_j-t_{\pi(j)}.
\tag{4}
\]
The recursion gives \(y_j-y_{j-1}\ge\gamma\). Induction also gives
\[
t_{\pi(j)}-\delta\le y_j
\le t_{\pi(j)}-\delta+(j-1)\gamma
\le t_{\pi(j)}+\delta.
\tag{5}
\]
For the induction step, use the previous upper bound and
\(t_{\pi(j-1)}\le t_{\pi(j)}\) in the second argument of the maximum in
(3). This proves \(\|D\|_2\le\delta\).

The eigenvalues of the diagonal part after (4), in increasing order, are the
numbers \(y_1,\ldots,y_n\). If \(\mu_1\le\cdots\le\mu_n\) are the
eigenvalues after adding \(R\), the Hermitian min–max principle gives
\[
|\mu_j-y_j|\le\|R\|_2\le\eta.
\]
Consequently every adjacent gap is at least
\[
\mu_{j+1}-\mu_j\ge\gamma-2\eta
\ge\frac{\delta}{n-1}>0
\]
under (1). All nonadjacent gaps are sums of adjacent gaps, proving (2).
Sorting is the only superlinear step. For a complex tridiagonal matrix, each
absolute off-diagonal value is obtained from one allowed nonnegative square
root of the sum of squares of its real and imaginary parts. No extraction of
bits from exact real inputs occurs. \(\square\)

The sorting is an internal computation: the output (4) uses the original
indices, so adding \(D\) preserves the input tridiagonal structure.

## 3. Unrestricted order two

For
\[
T=\begin{pmatrix}t_1&b\\\overline b&t_2\end{pmatrix},
\]
subtract \(\delta\) from the smaller diagonal entry and add \(\delta\) to
the larger one, breaking a tie arbitrarily. The new diagonal difference has
absolute value at least \(2\delta\). The eigenvalue gap is therefore
\[
\sqrt{(T'_{11}-T'_{22})^2+4|b|^2}\ge2\delta.
\]
This uses constant work and has no restriction on \(b\).

## 4. What is not proved

For general normalized tridiagonal input, the off-diagonal norm may be of
order one, rather than order \(\delta/n\). Then the bound
\(\gamma-2\eta\) is useless. No valid argument removing (1) is supplied.
The construction is therefore not a solution to the nearly-linear deterministic
Minami problem in KE-02. It must not be used to mark that entry SOLVED.

Source for the full target: the KE-02 README at commit
`f41f1f9ffa2171550d4bb795862c6170c4f26070`, with provenance in
`sources/snapshot.json`. The additional hypothesis (1) belongs to this note,
not to the repository's original problem.
