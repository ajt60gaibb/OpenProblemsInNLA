# SP-12 source route and additional formal proof gates

Prepared by `/root/fr05_statement` (OpenAI Codex AI agent), 18 October 2026. This report was developed before implementation; it specifies obligations and a proposed formal adaptation, not completed theorems. The exact fresh statement approval is in STATEMENT_REVIEW_1.md; reviewed-inputs.json binds original, statement, reuse and API inputs. No SP-11 source or original SP-12 artifact is modified by this report.

## Primary-source chain checked

Hall's versioned primary text is https://arxiv.org/html/2601.01211v1. Sections 3.3–3.7 define the required local independence, upper-zero genericity and SAP implication; Section 5.6 closes the polynomial construction. Full general position is stronger than needed and need not exist in minimum-degree-complementary dimension. The actual local input families suffice. The canonical application note supplies the full induced-extension argument and the critical-coloring deduction, including rank-zero/disconnected cases. The independent historical review was checked as corroboration, not substituted for the primary argument. The abstract's positive-definite wording must not replace PSD.

A saved web-tool rendered-excerpt snapshot is hash-bound in reviewed-inputs.json. It is not a raw HTML/PDF digest. Direct shell download failed DNS resolution, so no raw primary-file hash is claimed.

## Reuse and exact new obligations

The existing SP-11 polynomial construction, finite shared-variable noncancellation, greedy ordering and real simultaneous evaluation can be reused unchanged. SP11.target itself discards information needed here; use the actual polynomial vectors and evaluation witness. No new leading-monomial theorem or stronger general-position premise is necessary.

1. **Actual real recurrence.** Evaluation of weighted determinant minors equals the real weighted form with the evaluated coefficients, by RingHom.map_det. Evaluation of coordinate contraction then commutes with the finite well-founded LSS recursion. This must hold for the actual shared coefficient assignment, rather than an unrelated family of real vectors.
2. **Actual predecessor independence.** A dependent family w makes every contraction coordinate vanish. Apply AlternatingMap.map_linearDependent to Fin.cons y w, whose independence would imply independence of w by restriction. Existing nonzero evaluated diagonal vectors therefore force each actual W_j input family linearly independent.
3. **Gram PSD and SAP.** For a faithful real factor R with independent earlier-nonneighbor rows, prove SAP by a maximal nonzero column of a symmetric test matrix X. Its coefficients are supported on W_j. Gram kernel equality turns AX=0 into a zero combination of those representing rows, so independence kills the column. Equivalently, prove upper-zero genericity and its SAP implication. Prove generic SAP invariance under simultaneous index equivalences and bridge the identical SP11/SP12 pattern definitions. Gram PSD is automatic, and gram_rank_le retains the exact dimension bound.
4. **Strong Delta factor API.** For every h and graph G on Fin h, obtain d and real R with d+SP11.MinimumDegree G≤h, SP12.HasPattern G (gram R), and SP12.StrongArnold(gram R). Treat h=0 explicitly if needed for induction. PSD is a separate general Gram lemma. This is genuine PSD/SAP Strong Delta, not the ordinary SP11 conclusion.
5. **Induced-vertex extension.** Given the preceding Gram-pattern/SAP factor for the induced graph on old vertices, produce an exact-pattern/SAP factor in dimension d+1 after adding one vertex. The extension must handle arbitrary new adjacency, disconnected graphs and d=0. A block diagonal matrix alone misses new edges; an arbitrary perturbation can destroy exact old nonedges or SAP. This is a real new obligation.
6. **Chromatic discrete bridge.** Use the actual frozen natural proper-color minimum. Either select a vertex-minimal induced subgraph with equal chromatic number and minimum degree at least chi−1, then extend; or induct on vertex count, deleting a vertex of degree less than chi−1 while preserving chi, then extend the inductive factor. A color missing from that vertex's neighbor-color image extends a coloring. The low-degree step, relabeling and natural-subtraction accounting must be proved; no criticality premise may remain in Target.

Greedegree alone cannot replace gate 5 or 6. For instance, a triangle with a pendant at each triangle vertex has chromatic number 3 but every MCS ordering leaves a degree-1 pendant last. This example was independently reasoned through here and by the root agent; it is a route obstruction, not evidence against the target.

## Proposed analytic adaptation: Gram factors rather than a rank-stratum manifold

The following is our formalization design, not a claim already proved in Mathlib. Let N index unordered old nonedges i<j and F(R)_(i,j)=sum_a R_i,a R_j,a. Its derivative sends S to the nonedge entries of RS^T+SR^T. SAP of RR^T should imply this derivative is onto. Identify a functional on the nonedge-coordinate space with coefficients, extend them to a symmetric zero-diagonal matrix X supported on nonedges, and pair it with the derivative. Vanishing of that pairing for every S gives XR=0; hence RR^T X=0 and SAP gives X=0. Algebraic dual injectivity avoids imposing a Hilbert norm on the plain finite Pi matrix types. Full column rank of R is not needed.

A surjective strict derivative maps the neighborhood filter at R onto that at F(R)=0. Choose neighborhoods in b and R' where old edge entries remain nonzero and where the SAP test map for the larger graph remains injective. The desired old-nonedge coordinates −b_i b_j approach zero with b=epsilon*z, where z is the new adjacency indicator. A small nonzero epsilon puts that target in F(U_R), yielding R' in the chosen neighborhood. New Gram rows are (1,0) and (b_i,R'_i); old nonedges cancel exactly and new edge entries equal b_i. Dimension is d+1, so rank≤d+1 is enough; exact rank preservation and a continuous selection R'_epsilon are unnecessary.

For SAP openness, fix the finite-dimensional subspace Z_G of symmetric matrices supported on off-diagonal nonedges of the larger graph. At diag(1,RR^T), X↦BX is injective on Z_G by old SAP. Openness of injective continuous linear maps preserves it nearby. Exact pattern then makes this condition precisely the frozen StrongArnold predicate. This approach avoids formalizing the rank-r PSD manifold used by the application note while preserving its essential perturbation logic.

## Exact pinned Mathlib APIs inspected

- AlternatingMap.map_linearDependent: LinearAlgebra/Alternating/Basic.lean:784.
- LinearIndependent.comp and linearIndepOn_range_iff: LinearAlgebra/LinearIndependent/Defs.lean:203,380.
- Matrix.posSemidef_self_mul_conjTranspose and posSemidef_iff_dotProduct_mulVec: LinearAlgebra/Matrix/PosDef.lean:365,297.
- RingHom.map_det: LinearAlgebra/Matrix/Determinant/Basic.lean:318.
- LinearMap.dualMap_injective_iff: LinearAlgebra/Dual/Lemmas.lean:930.
- HasStrictFDerivAt.map_nhds_eq_of_surj: Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean:85; requires complete domain/codomain and derivative range top.
- ContinuousLinearMap.isOpen_injective: Analysis/Normed/Module/FiniteDimension.lean:270; finite-dimensional domain over a complete field.
- hasStrictFDerivAt_apply and hasStrictFDerivAt_pi: Analysis/Calculus/FDeriv/Prod.lean:368,372.
- HasStrictFDerivAt.mul, .sum: Analysis/Calculus/FDeriv/Mul.lean:177 and FDeriv/Add.lean:409.
- LinearMap.toContinuousLinearMap and continuous_of_finiteDimensional: Topology/Algebra/Module/FiniteDimension.lean:306,283.
- Filter.image_mem_map: Order/Filter/Map.lean:60.
- Nat.sInf_def/sInf_mem: Order/Lattice/Nat.lean:37,80.
- SimpleGraph.Colorable.chromaticNumber_eq_sInf and colorable_chromaticNumber_of_fintype: Combinatorics/SimpleGraph/Coloring/Vertex.lean:239,366. Mathlib's chromaticNumber is ENat, so an explicit equivalence to the frozen Nat definition is needed if these APIs are used. Direct Nat color-count lemmas may be simpler.

The manifest hashes the actual pinned files. These inspected APIs support the proposed route; they do not themselves prove the graph-specific derivative pairing, SAP openness equivalence, exact vertex extension, color-deletion theorem or full Target.
