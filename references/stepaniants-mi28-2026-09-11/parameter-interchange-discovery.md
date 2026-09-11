# MI-28: closure of the remaining parameter strip

**Proposed completion, independently derived by a separate Codex agent on 11 September 2026.** This note supplies the missing step for `/tmp/mi28_partial.md`. It is submitted for immediate cross-check before a full-resolution claim.

Use the partial note's notation: \(A,B>0\), \(D=|AB|=(BA^2B)^{1/2}\). Its norm reduction asks for

\[
D^p\le A^k\quad\Longrightarrow\quad B^p\le A^{k-p}.
\tag{N}
\]

The partial note proves (N) when \(\kappa>0\) and \(\kappa/(\kappa+1)\le\rho\le1\), with \(k=\kappa,p=\rho\). Call this previously verified parameter range Region 1.

## Inversion and parameter interchange

Suppose \(0<p\le k\le1\) and \(D^p\le A^k\). Set

\[
\widehat A=D^{-1},\qquad \widehat B=B.
\]

These matrices are positive definite, and

\[
|\widehat A\widehat B|^2
=B D^{-2}B
=B(B^{-1}A^{-2}B^{-1})B
=A^{-2}.
\]

The unique positive square root therefore gives

\[
|\widehat A\widehat B|=A^{-1}.
\tag{1}
\]

Invert the assumed order inequality. In terms of the transformed pair,

\[
|\widehat A\widehat B|^{k}
=A^{-k}\le D^{-p}=\widehat A^{p}.
\tag{2}
\]

Apply Region 1 to \((\widehat A,\widehat B)\) with the **swapped** parameters

\[
\kappa=p,\qquad \rho=k.
\]

Its hypotheses hold: \(\kappa>0\), \(0<\rho\le1\), and
\(\rho=k\ge p\ge p/(p+1)=\kappa/(\kappa+1)\).
The conclusion of Region 1 is

\[
B^{k}\le\widehat A^{p-k}=D^{k-p}.
\tag{3}
\]

The two exponents \(p/k\) and \((k-p)/k\) belong to \([0,1]\). Two applications of the Löwner–Heinz inequality—first to (3), then to the original premise—give

\[
B^p\le D^{p(k-p)/k}\le A^{k-p}.
\tag{4}
\]

Thus (N) holds for every \(0<p\le k\le1\), including its boundary \(p=k\). No negative or greater-than-one power is used in an order-preserving step.

## Consequence for the full target

The remaining strip of the partial note,

\[
0<k<1,\qquad k/2<p<k/(k+1),
\]

lies strictly inside \(0<p<k<1\), so (4) closes it completely. Together with the partial note's independently checked Regions 1 and 3 and the correctly attributed published region \(k\ge2p\), this proves the norm inequality for all \(k>0,0<p\le2\). The exterior-power argument then proves the stated log-majorization and hence the entire canonical determinant inequality. The \(p=0\) case is equality, and \(k=0\) follows by continuity as already recorded in the partial note.

The transformation here is **not** simultaneous inversion of \(A\) and \(B\), which merely preserves the original parameters. It replaces the base matrix by \(D^{-1}\), leaves \(B\) unchanged, and exchanges the base-power and modulus-power parameters. Identity (1) is the reason this gives new coverage.
