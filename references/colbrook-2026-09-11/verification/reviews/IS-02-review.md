# IS-02 independent agent proof review

**Verdict: PASS — full negative resolution of the exact displayed README target.**

**Review date:** 11 September 2026.  
**Reviewer:** separate Codex review agent `/root/review_counterexamples`.  
**Canonical target:** `eigenvalues-and-inverse-problems/IS-02/README.md`, “Problem statement”.  
**Manuscript:** `eigenvalues-and-inverse-problems/IS-02/solution.md`, Theorem IS-02 and sections 1–2.

This is an independent agent audit of the complete mathematical argument, not a rerun of the submitted diagnostic script. It is not external human peer review or a formal proof certificate. The reviewer did not edit the manuscript, the problem statement, status metadata, diagnostic code, or remotes.

## Reviewed proof identity

The hashed block starts at the first `## Theorem ` and ends immediately before `## Scope and review notes`. Line endings were normalized to LF, leading and trailing whitespace stripped, and the resulting text encoded as UTF-8 without a BOM.

- SHA-256: `6473c2bf8ddb83ac758e845135aa400faffbc53a12c88eb4809208d9df66a39b`
- UTF-8 length: 3,031 bytes.

The verdict applies to this proof block and the canonical mathematical target read on the review date. Notices outside the block are not mathematical premises of the review.

## Exact target and conclusion

The target asserts that, for every integer $n\geq4$, a symmetric entrywise nonnegative row-stochastic matrix with positive trace which is determined by its spectrum up to permutation similarity must lie in

\[
[I_n,C_n]\cup\bigcup_{V\in\operatorname{vert}(\mathcal S_n)}
([I_n,V]\cup[C_n,V]),\qquad
C_n=(\mathbf1\mathbf1^T-I_n)/(n-1).
\]

The manuscript supplies an order-four matrix satisfying the antecedent and lying outside the entire union. One allowed dimension suffices to disprove this universally quantified implication. No classification in other dimensions is required.

As a source cross-check, the positive-trace condition and the three kinds of segments agree with Conjecture 5.1 on manuscript page 10 of [Mourad–Abbas](https://arxiv.org/pdf/1310.1273). The local README is the canonical target for this verdict.

## Complete proof checks

Let

\[
S=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
J=\tfrac12\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
A=\operatorname{diag}(S,J).
\]

Both blocks are symmetric, nonnegative, and row-stochastic. Their spectra are respectively $\{1,-1\}$ and $\{1,0\}$; hence $\sigma(A)=\{1,1,0,-1\}$ with multiplicities and $\operatorname{tr}A=1>0$.

### 1. Spectral uniqueness among all admissible matrices

Take any $B\in\mathcal S_4$ with this spectrum. No restriction on its support or block structure is assumed. Symmetry gives column sums one as well as row sums one, so expansion verifies

\[
x^T(I-B)x=\tfrac12\sum_{i,j}b_{ij}(x_i-x_j)^2.
\]

Every term is nonnegative. Therefore $Bx=x$ implies that $x$ is constant along every positive off-diagonal edge and hence on each connected component. Conversely, a vector constant on each component satisfies $Bx=x$, because there are no entries between components and each component retains row sums one. Thus the eigenspace for eigenvalue one has dimension equal to the number of components. Because $B$ is real symmetric, algebraic and geometric multiplicities agree. Its two eigenvalues equal to one force exactly two nonempty components.

At least one component block $D$ has eigenvalue $-1$. Restrict a real $-1$ eigenvector to a component where it is nonzero; the restriction is still an eigenvector of that block. The second identity is also correct:

\[
0=z^T(I+D)z=\tfrac12\sum_{i,j}d_{ij}(z_i+z_j)^2.
\]

Every positive off-diagonal edge forces $z_i=-z_j$. Starting from a nonzero coordinate and using connectivity proves that every coordinate on this component is nonzero and has the same absolute value. A positive diagonal entry would then force $z_i=0$, which is impossible. There are therefore no positive diagonal entries, and all positive edges cross between the positive and negative sign classes $P,N$.

The total cross weight calculated from $P$ is

\[
\sum_{i\in P,j\in N}d_{ij}=|P|,
\]

because each row sums to one and there is no within-class weight. Calculating from $N$ gives $|N|$, and symmetry makes the totals equal. Hence $|P|=|N|$, so this component has even order. This conclusion uses symmetry essentially; bipartiteness alone would not justify equal class sizes.

There are four vertices and exactly two nonempty components. The component carrying $-1$ cannot have order four, and its even positive order is consequently two. The other component also has order two. This explicitly excludes the potential $1+3$ decomposition.

Every symmetric nonnegative row-stochastic $2\times2$ block is

\[
B(t)=\begin{pmatrix}t&1-t\\1-t&t\end{pmatrix},\qquad
0\leq t\leq1,
\]

with eigenvalues $1,2t-1$. The block carrying $-1$ is $B(0)=S$. The remaining spectrum is $\{1,0\}$, so the other block is $B(1/2)=J$. Relabeling the components and their vertices therefore transforms every such $B$ into $A$. This proves the full spectral-uniqueness requirement, including multiplicities.

### 2. Exclusion from all proposed segments

The decomposition

\[
A=\tfrac12\operatorname{diag}(S,I_2)
 +\tfrac12\operatorname{diag}(S,S)
\]

has distinct endpoints, both lying in $\mathcal S_4$. Thus $A$ is not an extreme point. The endpoints need not be identified as vertices; membership in the polytope and distinctness suffice.

For an arbitrary vertex $V$, if $A=(1-t)I_4+tV$ with $0\leq t\leq1$, then

\[
0=A_{11}=1-t+tV_{11}.
\]

Both summands are nonnegative, so $t=1$. That would make $A=V$, contrary to the preceding decomposition. Likewise, from $A=(1-t)C_4+tV$,

\[
0=A_{13}=(1-t)/3+tV_{13}
\]

forces $t=1$ and the same contradiction. These arguments use only entrywise nonnegativity of $V$; they cover every extreme point, including vertices which are not permutation matrices.

Finally, $A=(1-t)I_4+tC_4$ would imply $0=A_{13}=t/3$, so $t=0$ and $A=I_4$, which is false. All three parts of the asserted locus, including their endpoints, have been excluded.

## Adversarial checks and limitations

I specifically checked for an overlooked irreducible cospectral matrix, a $1+3$ component partition, a $-1$ eigenvector with zero coordinates, self-loops on the $-1$ component, unequal bipartition sizes, and non-permutation vertices of the polytope. The proof excludes each possibility as detailed above. No material gap or false intermediate claim was found.

The PASS verdict concerns the exact necessary condition in the README. It does not assert an all-dimensional spectral-uniqueness classification, a result under strict entrywise positivity, literature novelty, publication, or priority. The argument was checked mathematically by a separate agent; no external human referee or formal theorem prover has certified it.
