# IV-06: exact statement and numerical targets before proofs

This is a statement-only candidate for the complete original component-count conjecture. The mathematical counterexample is Matthew J. Colbrook's; formalization is prepared for George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI assistance. No contact email is added. No proof implementation may begin until two independent statement approvals bind the compiled definitions and Challenge.

The source is the complete canonical IV-06 page, complete authored and submitted manuscripts, shared submitted preamble, and complete independent informal review at actual upstream revision `f41f1f9ffa2171550d4bb795862c6170c4f26070`. Source hashes, exact locators and observed duplicate-audit scope will be retained in the package.

## Complete original target and genuine definitions

For every positive integer n and every pair of real n×n matrices L,U satisfying Lᵢⱼ≤Uᵢⱼ for every entry, the actual interval family consists of **all** matrices A with Lᵢⱼ≤Aᵢⱼ≤Uᵢⱼ independently for all i,j. Singleton intervals are permitted. The family is not restricted to symmetric, diagonalizable or irreducible matrices.

The attained real-eigenvalue set is exactly

\[
S(L,U)=\{\lambda\in\mathbb R:\exists A,\ L\le A\le U\text{ entrywise},\ \exists v\in\mathbb R^n\setminus\{0\},\ Av=\lambda v\}.
\]

The eigenvector condition uses actual real Matrix.mulVec, scalar multiplication and a nonzero vector. A generic theorem must prove its equivalence with det(λI−A)=0; determinant zero is not silently substituted without a bridge. No assumption that other eigenvalues are real is introduced.

The component count is the **cardinal of Mathlib's actual ConnectedComponents quotient of the subtype S(L,U)** with its subspace topology from ℝ. It is not Nat.card, which would collapse infinite types to zero, and no finiteness or compactness assumption is inserted. The universal conjecture is exactly

\[
\forall n\ge1\;\forall L,U,\ L\le U\Longrightarrow
\#\operatorname{ConnectedComponents}(S(L,U))\le n.
\]

The final export negates this entire universal statement. The canonical equivalent description as a union of at most n closed intervals is retained in the source, but is not used to replace the component-count definition. No separate formal claim about general interval-union representation or the exact locations of every endpoint is needed.

## Exact independent-entry counterexample

Use

\[
F(a,b)=\begin{pmatrix}25&a&b\\1&-1&0\\1&0&1\end{pmatrix},\quad
L=F(-166,9),\quad U=F(-16,159).
\]

Prove L≤U entrywise and the exact family identity

\[
A\in\mathcal A(L,U)\quad\Longleftrightarrow\quad
\exists a\in[-166,-16]\;\exists b\in[9,159],\ A=F(a,b).
\]

This is a theorem, not a restriction inserted into the definition of the original interval family. All seven fixed entries are forced by matching endpoints; the two variable entries remain independent.

Prove, for **every** real a,b,λ, the actual determinant identity

\[
\det(\lambda I-F(a,b))=(\lambda-25)(\lambda^2-1)-a(\lambda-1)-b(\lambda+1).
\]

This is exact polynomial algebra. No numerical matrix determinant or eigenvalue oracle is used.

## Four included points with actual nonzero eigenvectors

The fixed finite data, in zero-based Fin 4 order, are:

| index | λ | a | b | v | F(a,b)v |
| --- | --- | --- | --- | --- | --- |
| 0 | −3 | −21 | 154 | (−4,2,1) | (12,−6,−3) |
| 1 | 0 | −16 | 9 | (−1,−1,1) | (0,0,0) |
| 2 | 3 | −146 | 29 | (4,1,2) | (12,3,6) |
| 3 | 25 | −91 | 84 | (312,12,13) | (7800,300,325) |

Every a,b lies in its respective closed interval. Every vector is nonzero; the zero eigenvalue is allowed and still uses a nonzero vector. The export must prove all four actual matrix-vector equations and membership of all four λ in the actual attained set.

## Three universally excluded separators

In zero-based Fin 3 order, use separators (−1,1,12). For every A in the full independently varying interval family, prove the following actual determinant bounds:

| separator λ | lower bound | upper bound |
| --- | --- | --- |
| −1 | −332 | −32 |
| 1 | −318 | −18 |
| 12 | −3750 | −150 |

The bounds follow for **every** admissible parameter pair from the affine determinant formula and the two closed parameter intervals. The final proof need not numerically partition the box, compute eigenvalue branches, or prove the optional stronger assertion that every value between these determinant endpoints is attained. These bounds are sufficient to exclude determinant zero universally.

All three upper bounds are at most −18. The retained LeanCert task is the exact strict point inequality **(−18 : ℝ)<0**, explicitly in kernel mode, on a singleton domain. It must be consumed in proving all three actual determinant expressions negative and thus excluding all three separators from S(L,U), using the proved eigenvector/determinant bridge. This scalar check does not replace the exact matrix and full-box inequalities. No interval subdivision or approximate root enclosure is planned.

## Genuine topological separation and full negation

A generic theorem must prove: for any subset S of ℝ and points x,y of its subtype, equality of their actual ConnectedComponents classes implies Icc(x,y)⊆S. This is the actual connectedness-to-order-convexity fact from Mathlib, not an assumed property field in a custom component definition.

The exact ordering is −3<−1<0<1<3<12<25. For any two distinct included points, one excluded separator lies strictly between them. Consequently their actual component classes differ. Prove an injection of Fin 4 into ConnectedComponents(S(L,U)), with representatives equal to the four specified eigenvalues, and the resulting cardinal lower bound 4≤#ConnectedComponents(S(L,U)). Thus 3<#ConnectedComponents(S(L,U)), while dimension is exactly three. This complete admissible instance negates the entire canonical all-dimension bound.

The proof claims **at least** four components, not exactly four, and does not classify all endpoints or prove a sharp general replacement bound. Distinct eigenvalues of different admissible matrices legitimately lie in the union; the claim is not about one 3×3 matrix having four eigenvalues.

## Eight planned complete exports and trust

1. `eigenvalue_determinant_semantics`: genuine nonzero real eigenvector iff actual det(λI−A)=0, for all real square matrices (including the empty-dimensional convention where both sides are false).
2. `family_and_determinant_semantics`: original bounds admissibility, exact two-parameter description of the original full interval family, and the all-real determinant identity.
3. `witness_eigenpairs`: all four actual admissible nonzero integer eigenpairs and actual attained-set membership.
4. `witness_separators`: full-box determinant bounds, strict negative upper bounds and exclusion of all three separators, with retained kernel LeanCert use.
5. `connected_component_intervals`: genuine generic connected-component equality forces interval containment in the real subset.
6. `four_components`: exact representatives in four distinct actual components and the cardinal lower bound.
7. `counterexample`: valid original bounds and a strict dimension-three component-count violation.
8. `not_componentBoundConjecture`: unconditional full negation of the original universal target.

Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` are to be pinned. The only allowed transitive axioms are propext, Classical.choice and Quot.sound. No source theorem, topology fact, determinant bridge, family property or numerical certificate may be added as an axiom or unproved hypothesis. Challenge alone has eight deliberate placeholders; no Proof or Solution implementation exists at statement freeze. Solution is registered as a library in the initial config, while the initial default remains Challenge.

Independent exact arithmetic diagnostics validate the proposed statements but are not trusted premises. Two independent statement approvals, complete proof, two independent final proof reviews, actual Linux Comparator/default-kernel verification with controls and an independent operational audit are required before any status promotion.
