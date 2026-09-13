# The quadratic correlation matrix need not have full nonnegative rank

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. Developed with ChatGPT assistance. See [submission and review record](README.md).

## 1. The result

Let \([n]=\{1,\ldots,n\}\), and index rows and columns by all subsets of \([n]\). Define

\[
C_n(a,b)=(1-|a\cap b|)^2.
\]
Every entry is fixed by this formula. Nonnegative rank is taken over the real numbers.

**Theorem.** For every integer \(n\ge1\),

\[
\operatorname{rank}_+(C_n)
\le\min\left\{2^n,\;2^{n-1}+n+\binom n2+\binom n4\right\}.
\]

Consequently, \(\operatorname{rank}_+(C_7)\le127<128\), and \(\operatorname{rank}_+(C_n)<2^n\) for every \(n\ge7\). This disproves the universal equality asked in NR-03.

The proof supplies nonnegative **rational** factors, which in particular are valid real factors. It does not determine the exact nonnegative rank of \(C_7\).

## 2. Four families of rank-one matrices

For a column index \(b\), set

\[
p=|b|,\qquad d_b=\max\{1,(p-1)^2\}.
\]

Thus \(d_b>0\), including the exceptional singleton columns where \((p-1)^2=0\). Let \(a^c=[n]\setminus a\), and select one representative from every complementary pair:

\[
\mathcal A=\{s\subseteq[n]:n\notin s\},\qquad |\mathcal A|=2^{n-1}.
\]

For a four-element set \(T\), define the nonnegative row function

\[
h_T(a)=\max\{|a\cap T|-2,0\}.
\]

Write \(\mathbf1_E\) for the indicator of a statement \(E\). Form a left matrix \(W\) and an integer-scaled right matrix \(V\) with the following atom families:

**Complementary pairs, one atom for each \(s\in\mathcal A\):**

\[
W_{a,s}=\mathbf1_{\{a=s\text{ or }a=s^c\}},\qquad
V_{s,b}=(1-|s\cap b|)^2(1-|s^c\cap b|)^2.
\]

**Singleton corrections, one atom for each \(i\in[n]\):**

\[
W_{a,i}=\mathbf1_{\{i\notin a\}},\qquad
V_{i,b}=\mathbf1_{\{b=\{i\}\}}.
\]

**Pairs, one atom for each \(S\in\binom{[n]}2\):**

\[
W_{a,S}=\mathbf1_{\{S\subseteq a\}},\qquad
V_{S,b}=4(p-2)\mathbf1_{\{S\subseteq b\}}.
\]

**Four-element sets, one atom for each \(T\in\binom{[n]}4\):**

\[
W_{a,T}=h_T(a),\qquad
V_{T,b}=12\mathbf1_{\{T\subseteq b\}}.
\]

The four families are disjoint sets of atom indices. All factors are nonnegative. For the pair family, a nonzero indicator forces \(p\ge2\), so the apparently signed coefficient \(p-2\) cannot produce a negative entry.

There are exactly

\[
r(n)=2^{n-1}+n+\binom n2+\binom n4
\]

listed atoms. We will prove

\[
WV=C_n\operatorname{diag}(d_b).
\]

Since all \(d_b\) are positive, setting \(H_{k,b}=V_{k,b}/d_b\) gives an actual nonnegative factorization \(C_n=WH\) with \(r(n)\) terms.

## 3. Exact entrywise verification

Fix \(a,b\), and put \(t=|a\cap b|\), \(p=|b|\). Then \(|a^c\cap b|=p-t\).

Exactly one complementary pair contains \(a\). Its contribution to \((WV)_{a,b}\) is

\[
G=(t-1)^2(p-t-1)^2.
\]

The singleton contribution is

\[
E=\mathbf1_{\{p=1\}}(1-t).
\]

The pair contribution is

\[
P=4(p-2)\binom t2.
\]

For the four-set contribution, a set \(T\subseteq b\) contributes one unit to \(h_T(a)\) when it meets \(a\) in exactly three elements, two units when it meets \(a\) in four elements, and zero otherwise. Therefore

\[
Q=12\left((p-t)\binom t3+2\binom t4\right).
\]

If \(p=0\), then \(t=0\), and \((G,E,P,Q)=(1,0,0,0)\), as required. If \(p=1\), then \(t\in\{0,1\}\), \(G=P=Q=0\), and \(E=1-t=(1-t)^2\), again as required.

For \(p\ge2\), we have \(d_b=(p-1)^2\) and \(E=0\). The polynomial identity

\[
\begin{aligned}
&(p-1)^2(t-1)^2-(t-1)^2(p-t-1)^2\\
&\quad=t(t-1)^2(2p-2-t)\\
&\quad=2(p-2)t(t-1)
 +2(p-t)t(t-1)(t-2)
 +t(t-1)(t-2)(t-3)\\
&\quad=4(p-2)\binom t2+12(p-t)\binom t3+24\binom t4
\end{aligned}
\]

shows that \(G+P+Q=d_b(t-1)^2\). Thus, in every case,

\[
(WV)_{a,b}=d_b(1-|a\cap b|)^2.
\]

This proves the announced factorization. The alternative trivial factorization \(C_n=I_{2^n}C_n\) gives the minimum with \(2^n\) in the theorem.

## 4. Why this is a strict counterexample for every n >= 7

Let

\[
p_n=n+\binom n2+\binom n4.
\]

At \(n=7\), \(p_7=7+21+35=63<64\), so

\[
r(7)=64+63=127<128.
\]

Pascal's identities give

\[
p_{n+1}-2p_n=1-\binom n2+\binom n3-\binom n4.
\]

For \(n\ge7\),

\[
\binom n4=\frac{n-3}{4}\binom n3\ge\binom n3,
\]

and hence \(p_{n+1}<2p_n\). Induction from \(p_7<2^6\) yields \(p_n<2^{n-1}\) for all \(n\ge7\). Therefore

\[
\boxed{\operatorname{rank}_+(C_n)\le r(n)<2^n\quad(n\ge7).}
\]

Also,

\[
\frac{\operatorname{rank}_+(C_n)}{2^n}
\le\frac12+\frac{n+\binom n2+\binom n4}{2^n}
=\frac12+O(n^4 2^{-n}).
\]

This is an upper bound, not an assertion about the actual limiting ratio.

## 5. Scope

An explicit counterexample at one allowed integer disproves a universally quantified equality. The construction gives one at \(n=7\), and the bound gives counterexamples at every larger integer. No assertion of exact rank 127 or minimal counterexample dimension is needed.

The result concerns this prescribed submatrix, not an arbitrary completion of unique disjointness. It also does not give the extension complexity of the entire correlation polytope: a factorization of a submatrix need not extend to the full slack matrix.

The earlier proof of \(\operatorname{rank}_+(C_4)=16\) is compatible with the construction. Here the nontrivial expression gives 19 terms for \(n=4\), 36 for \(n=5\), and 68 for \(n=6\), so it does not improve the trivial bounds at those sizes. The universal question is nevertheless settled negatively.

## 6. Reproducibility and sources

`data/factors_n7.json` contains all factors and denominators. `code/verify_certificate.py` checks every entry without importing the generator. `code/verify_minimal.py` is a second, short checker. The analytic identity above has an exact coefficient check in `code/self_tests.py`; the same suite checks every entry for n=1,...,9 and checks the rational CSV product directly. Optional C++ verification reads the CSV data independently.

For primary references and the repository's evidence-status definitions, see `SOURCES.md`. The complete proof passed a separate [independent Codex AI-agent informal audit](independent-review.md) on 13 September 2026. No external human peer review or formal verification is claimed. No Lean verification was performed.
