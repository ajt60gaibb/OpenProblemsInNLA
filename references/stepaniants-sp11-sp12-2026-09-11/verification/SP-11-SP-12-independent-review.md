# Independent review of the reconstructed SP-11 and SP-12 notes

Reviewer: Codex independent agent `/root/review_md03_md04`.
Review date: 11 September 2026 (UTC).

**Verdict: PASS for both exact canonical mathematical targets.** I independently read and checked both supplied deductions and the essential all-graph proof in H. Tracy Hall's arXiv:2601.01211v1, including its central non-cancellation induction. I found no gap in the dependency chain needed here. This supports a literature-dependent Solved classification under this repository's published status convention, subject separately to the parent's submission-eligibility audit. This is an independent automated-agent mathematical review, not human peer review, formal verification, a journal acceptance statement, or a claim that the reviewed application notes are new discoveries.

The substantive Strong Delta Theorem is Hall's result. George Stepaniants may be identified as the author of the application notes, with Department of Computing and Mathematical Sciences, California Institute of Technology, but must not be credited with Hall's theorem or an original resolution of these conjectures. No personal email is included here.

## Exact reviewed files and scope

Read-only source directory: `/Users/georgestepaniants/Downloads/OpenProblemsInNLA_reconstructed_notes`.

| Source | Bytes | SHA-256 |
|---|---:|---|
| `notes/SP-11.md` | 2388 | `3a1c7925846cf098a23af2ce46cb5a0b27f620eb46f04bf472d4233ace962416` |
| `notes/SP-12.md` | 5236 | `402921c079bf0cafc94020e806a5e42be4667147411b56ade228be0b7a28b61e` |
| `README.md` | 2073 | `a551ca774e53b451abaa8e5aecaea18694e5c4129fd3aa10f17df7ecce27be93` |
| `SOURCES.md` | 1824 | `0b6ff4d162f6f7b68795c5a4155ae1c6ec202d9ed32efb6750ac4dc240b6391b` |
| `STATUS.json` | 784 | `2d031dac177b47b4336013ca432c2660f28dd9cfbc7f12246251b50894ece40e` |

The exact canonical targets were read in `/tmp/nla-mf22-worktree/eigenvalues-and-inverse-problems/SP-11/README.md` and the corresponding SP-12 file. SP-11 allows arbitrary real symmetric matrices with the exact off-diagonal graph pattern and unrestricted diagonal; its target is maximum nullity at least minimum degree. SP-12 requires positive semidefiniteness and SAP, with target nullity at least chromatic number minus one. The notes address these precise targets for all finite simple undirected graphs with at least one vertex.

The package correctly withdraws unsupported prior claims about missing saved artifacts, graph-atlas runs, code, and manifests. I did not perform or certify any graph-atlas enumeration. Those claims must remain withdrawn. The package's preparation-stage eligibility and review limitations should be retained as historical provenance, with this later review and the parent's actual network audit recorded separately. The package's date metadata is not evidence that checks were performed on that later date.

## Primary source and extent of source review

[H. Tracy Hall, *The Delta Theorem: A dimension bound for faithful orthogonal graph representations*, arXiv:2601.01211v1](https://arxiv.org/html/2601.01211v1), submitted 3 January 2026. The [current arXiv record](https://arxiv.org/abs/2601.01211) showed only v1 when checked during this review; no withdrawal was displayed.

I read the definitions and main dependency chain in Sections 2–5: the exact-pattern PSD/SAP definitions; uniform LSS; weak and strong success; Proposition 3.9; Proposition 3.11 and Theorem 3.12; the alternating-tensor polynomial construction of Section 4; the recursive diagrams of Section 5.1; the greedy-order inequalities of Sections 5.3–5.4; the complete proof of Lemma 5.14; and the proof of Theorem 3.20 in Section 5.6. I checked how Corollaries 3.21–3.24 follow. I did not attempt to certify the separate NP-hardness appendix, field extensions, or other concluding generalizations, none of which is needed for these notes.

The following is my own reconstruction of the key checks. It supplies the details that make the review more than a theorem-title or abstract check.

## Reconstructing the essential all-graph argument

### 1. The greedy inequalities and permitted colors

Fix a maximum-cardinality-search ordering of the vertices. In the complement graph, let $k_i(v_j)$ count neighbors of $v_j$ among vertices preceding stage $i$, and set $k_j=k_j(v_j)$. Greediness says

$$k_i\le k_i(v_j)\le k_j\qquad(i\le j).$$

In particular $k_j$ is nondecreasing. Set $d=k_n+1=n-\deg(v_n)$. Every alternating node has at most $d$ incident conduits.

If $W_j=(w_1,\ldots,w_{k_j})$ lists earlier nonneighbors, then $w_s=v_i$ has exactly $s-1$ predecessors among that list. Consequently

$$k_i\le k_i(v_j)=s-1.$$

For an earlier neighbor $v_i$ of $v_j$, insert $v_i$ into the ordered list $W_j$ at position $s$. The same inequality $k_i\le s-1$ holds. These two elementary inequalities are precisely what the coloring argument needs. The word **earlier** is essential in the second case; a source wording omission is recorded below.

### 2. Polynomial vectors, exact orthogonality, and repeated variables

For each vertex $j$, take an independent alternating $(k_j+1)$-tensor with freely variable coordinates on increasing index tuples. Contract its first $k_j$ slots against the already constructed vectors of $W_j$ to obtain $r_j\in\mathbb R^d$. This recursion is finite because all children have earlier vertex labels. Every coordinate of every $r_j$, and every inner product $r_i^T r_j$, is a polynomial in the finitely many independent tensor coordinates.

Alternation gives two exact facts: $r_j$ is orthogonal to each vector in $W_j$, and a linearly dependent list of input vectors gives $r_j=0$. These follow by evaluating the alternating form against an arbitrary final vector. They do not require a genericity assumption.

Expanding the recursion as a tree reuses the same tensor variables at every occurrence of a vertex label. It does not replace those occurrences by independent variables. This reuse is the possible source of cancellation, so it is essential that the next check deals with monomials in shared, commuting variables.

### 3. Why the highest monomial is unique despite reuse

Consider the double-root tree representing $r_i^T r_j$ for $i\le j$, where either $i=j$ or $v_i$ and $v_j$ are adjacent. All ordinary child lists contain distinct vertex labels. For $i<j$, regard the top $i$-node as an extra child of the top $j$-node and insert it into that node's child list in vertex order. Adjacency ensures that this augmented list also has distinct labels. If $i=j$, keep the two identical top nodes and their joining conduit as a separate symmetric case.

At an ordinary node, color the conduits to its children $1,\ldots,k$ in order. At the exceptional later root, color the augmented child list $1,\ldots,k_j+1$ in order. For equal roots, use ordinary child colors on both sides and color their joining conduit $k_j+1$.

Process vertex classes in increasing vertex order. Every occurrence of the next nonfinal class $u$ already has its lower conduits colored $1,\ldots,k_u$. If it occupies position $s$ in its parent's ordinary child list, previously processed siblings use exactly $1,\ldots,s-1$. Thus the smallest permitted upward color is $s$, and $k_u<s$ ensures that it does not repeat one of its own lower colors. In the exceptional augmented list, the same statement holds with its augmented position; an ordinary child's position can only increase, and the special earlier root satisfies the second greedy inequality above. These choices stay within $1,\ldots,d$.

The point requiring care is that priority is assigned to the **product** of variables of each class, not to individual node occurrences. Once all earlier classes have been fixed, every occurrence of class $u$ has the same fixed lower tuple $(1,\ldots,k_u)$ and a fixed lower bound $s$ on its upward color. Its independent tensor variable is therefore indexed by $(1,\ldots,k_u,a)$ with $a\ge s>k_u$. Increasing $a$ strictly lowers that variable in the specified lexicographic order. Choosing every occurrence's smallest allowed $a=s$ is simultaneously feasible. It individually maximizes each factor, so any changed occurrence strictly decreases the product in the multiplicative lexicographic monomial order; no other occurrence can increase its factor to compensate. This proves uniqueness of the entire class's choice, even with arbitrarily many reused occurrences. Induction fixes all conduits. At the final root there is no remaining choice, except the equal-root joining conduit, whose unique best color is $k_j+1$.

Hence one and only one coloring gives the maximal nonzero monomial, with coefficient $+1$ or $-1$. Its coefficient cannot cancel. This establishes the nonzero polynomial claim for every diagonal and every edge pair. The sign on the exceptional root is immaterial to nonvanishing.

### 4. From the polynomials to a PSD SAP witness

There are finitely many diagonal and edge polynomials. Their product is nonzero in a real polynomial ring, so one can choose a real parameter point at which all are nonzero. Thus every $r_j\ne0$, and $A=(r_i^T r_j)$ is real PSD with exactly the desired off-diagonal graph pattern.

Since $r_j\ne0$, the alternating contraction's vanishing-on-dependence property forces the vectors indexed by $W_j$ to be independent. Their principal Gram submatrix is therefore positive definite. Consequently the columns of $A$ at the positions of zeros above its $j$th diagonal entry are independent.

For completeness, this gives SAP directly. Suppose $X=X^T$, $AX=0$, $A\circ X=0$, and $I\circ X=0$, and choose the largest index $j$ of a nonzero column of $X$. Symmetry and the maximal choice imply that this column is supported strictly above its diagonal. The pattern equation puts that support among the zeros in column $j$ of $A$. It would therefore give a nontrivial linear relation among independent columns of $A$, contradicting $AX=0$.

Finally $\operatorname{rank}A\le d$, so

$$\operatorname{nullity}A\ge n-d=\deg(v_n)\ge\delta(G).$$

No equality of rank with $d$ is needed. The ordering exists for every finite graph, including disconnected graphs. For $n=1$ or $\delta(G)=0$, the target is also immediate.

This direct existence argument avoids relying on informal language about “reasonable” random distributions. The probabilistic formulation is consistent as well: for linearly independent inputs, contraction of an arbitrary alternating $(k+1)$-form onto its final slot is onto their orthogonal complement. After an orthonormal change of coordinates this follows by freely choosing the form's coordinates indexed by the first $k$ axes and one of the remaining axes. Choosing tensor coordinates with full-dimensional Gaussian laws therefore supplies conditional full-dimensional laws on the permissible subspaces. No additional probabilistic theorem is needed for the existence conclusion used by SP-11/SP-12.

## Nonessential issues in Hall's exposition

1. The abstract uses “positive definite” in describing a positive-nullity assertion. The definitions, Gram construction, and explicit statement in Section 6.2 use **positive semidefinite**. The reviewed conclusion is PSD. Reading the abstract literally as positive definite would be false, but that is not the mathematical theorem proved in the body.
2. Proposition 5.12 omits $i<j$ from its written hypotheses. Without it the proposition is false: take the path $v_1v_2v_3$ in its displayed greedy order, $j=2$, and $i=3$. Then $W_2$ is empty, $s=1$, and $k(v_3)=1\not<1$. Its proof and the immediately following Corollary 5.13 use the earlier-vertex case; Corollary 5.13 explicitly includes $i<j$. Every invocation in Lemma 5.14 has this valid scope. The restricted inequality was independently derived above, so the omission does not obstruct the main theorem.
3. The parenthetical at the start of Lemma 5.14 treats $|W_j|<d$ as enough to infer weak success from the existence of a nontrivial orthogonal complement. For the uniform construction, one must also exclude dependent input lists. That dependence is in fact excluded by the subsequently proved nonzero diagonal polynomials. The parenthetical is expressly unused, and the main proof does not rely on it. It should not be used as a substitute for the non-cancellation proof.

These are documented limitations of the exposition, not unfilled gaps in the necessary argument reconstructed above. I found no mathematical correction needed in either application note.

## SP-11 deduction

Hall's witness is a member of the larger real symmetric class allowed in SP-11. Forgetting PSD and SAP, rank-nullity immediately gives

$$\operatorname{mr}(G)\le\operatorname{rank}A=n-\operatorname{nullity}A\le n-\delta(G).$$

No connectedness assumption, prescribed edge weights, or diagonal restriction is inserted. Hall's Corollary 3.24 already identifies this ordinary Delta conclusion. The note's attribution is accurate.

## SP-12: independent audit of the submersion proof

Let $A\succeq0$ have rank $r$ and SAP with exact pattern $H$. In range/kernel coordinates, a local chart for the rank-$r$ PSD manifold is

$$
D(U,T)=\begin{pmatrix}U&T\\T^T&T^TU^{-1}T\end{pmatrix},\qquad U\succ0,
$$

near $(U,T)=(A|_{\operatorname{range}A},0)$. Its tangent space consists of the claimed blocks with arbitrary symmetric top block and arbitrary off-diagonal block. The orthogonal normal space, for the trace inner product, is exactly the symmetric matrices $X$ with $AX=0$.

The adjoint of the nonedge-entry map produces symmetric matrices supported on off-diagonal nonedges; a harmless factor of two in the trace inner product does not affect injectivity. If its restricted differential were not onto, a nonzero such normal matrix would violate SAP. Thus the submersion theorem provides a local smooth section, in particular $D_\epsilon\to A$ with the specified nonedge entries $-b_i b_j$.

The block matrix in the note is a congruence of $\operatorname{diag}(1,D_\epsilon)$, so both PSD and rank $r+1$ are exact. Old nonedges cancel, old edges stay nonzero by a finite continuity argument, and new edge coordinates are exactly the nonzero coordinates of $b=\epsilon z$.

For SAP, the fixed space $Z_G$ includes the required zero pattern independently of $\epsilon$. The map $X\mapsto\operatorname{diag}(1,A)X$ is injective there: its first row vanishes only if the first row and, by symmetry, first column of $X$ vanish; then SAP for $A$ eliminates the old block. This argument does not require the limiting matrix itself to have all the new nonzero edges. Finite-dimensional injectivity is open, so the perturbed exact-pattern matrix has SAP. Nullity is preserved.

The rank-zero case causes no manifold singularity because the fixed rank-zero stratum is the single point. Surjectivity then forces the nonedge-coordinate space to be zero; equivalently, $A=0$ with SAP cannot occur for an edgeless graph with two or more vertices. For $h=1$ the coordinate space is zero and the construction works directly; $h=0$, if allowed for the auxiliary lemma, is likewise vacuous. No step uses connectedness. Adding omitted vertices one at a time proves the stated induced-subgraph monotonicity.

The maximum defining $\nu(H)$ is attained: feasible PSD SAP matrices exist (for example, a sufficiently large positive diagonal added to an exact-pattern symmetric adjacency matrix gives a positive-definite matrix, which automatically has SAP), and attainable nullities form a nonempty finite subset of $\{0,\ldots,h\}$.

For $k=\chi(G)\ge2$, a vertex-minimal induced subgraph with chromatic number $k$ has minimum degree at least $k-1$ by the standard color-extension argument. Therefore

$$\nu(G)\ge\nu(H)\ge\delta(H)\ge k-1.$$

For $k=1$, nonnegativity suffices. This is the complete all-graph SP-12 target. No assumption of Hadwiger's conjecture is used. The implication from Strong Delta to this chromatic inequality was already stated as such in the problem's original literature; the application note appropriately makes no novelty claim.

## Limits and publication guidance

This review contains analytical checks, not numerical evidence or exhaustive graph enumeration. No unprovided prior artifact is verified. It does not settle submission eligibility, ownership, priority, or maintainer acceptance. Those are separate from the mathematical verdict.

When preparing a submission, preserve the original permanent IDs, paths, exact target text, and earlier attributed partial results. Describe the change as recording Hall's existing result and its explicit application, with George Stepaniants as author of the explanatory notes. Preserve the supplied snapshot and this review separately; update preparation-stage disclaimers only by adding accurate current-status metadata. Do not silently change the source snapshots or their hashes. Under the repository's distinction between independently checked and unchecked full claims, this full essential-proof review supports **Solved**, with the automated-agent verification limits stated openly.
