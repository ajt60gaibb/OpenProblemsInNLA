# Independent review of the IE-15 solution

**Verdict: PASS.** The argument establishes both canonical targets, g_RP(3)=3 and g_RP(4)=14/3, for real nonsingular matrices and every admissible rook path, including ties and growth at intermediate active matrices.

**Reviewer:** independent Codex agent `/root/prepare_manuscripts`.  
**Date:** 11 September 2026.  
**Reviewed canonical manuscript:** [IE-15 solution](../../../../linear-systems-and-elimination/IE-15/solution.md).  
**Canonical source SHA-256:** `5fdea54cbd8469bf3edac1fdcc7fb1cdb2f0c562bd06b45a7eaf3c792dd34dcf`.  
**Canonical mathematical-core SHA-256:** `94892294fd93f6725d85cfce30dd530ddc954e5a6e56db5274d95b2b4c2d69f1` (10,454 bytes; from the literal “All matrices are real” through the end of Section 5, before “## Scope and computational evidence”; includes the two layout-only `\Needspace` lines).  
**Layout-stripped canonical mathematical-core SHA-256:** `78c3ba86e9f02fb3b9dc1d1a74a5bf4e76a8b07ec151964e9f7f9a3ca90719fb` (10,397 bytes).  
**Preserved reviewed draft:** [original agent draft](../../original-agent-draft.md).  
**Original draft source SHA-256:** `50baa9e1e3547bdab04283dd1ba3e96e6622ab48960c5dad0ffb00d67ee325a8`.  
**Original draft mathematical-core SHA-256:** `cf113286c61f86c69181ddeab003f644c9798898e7361bf9d6ab7d01c3ae8481` (10,647 bytes; the same section boundaries before rendering-delimiter normalization).

This review independently checked the mathematical argument and exact witnesses. It is an agent review, not human peer review, a formal proof-assistant certificate, or a novelty certification. The repository's current target is the all-admissible-path definition; a narrower implementation with a prescribed pivot-search or tie-breaking rule is not asserted to have the same attained examples.

## Exact scope and normalization

The initial scaling is valid because the input is nonsingular and therefore has a positive maximum absolute entry. Applying the eventual row and column permutations at the outset reproduces the same diagonal pivot order; permutations made at later stages only reorder the remaining active indices and can be collected into those initial permutations. Every admissible pivot is nonzero. The factorization A=LDR consequently exists along the selected path.

The rook condition yields |L_ij|<=1 and |R_ij|<=1, because the active pivot column and row are p_j L_ij and p_j R_jk. No assumption that a pivot is the largest entry of the whole active matrix is introduced.

Multiplying original rows by pivot signs makes D positive via SA=(SLS)(SD)R. This preserves all active absolute values. Simultaneous diagonal row/column sign changes preserve positive pivots and make the last-row L entries nonnegative, including arbitrary choices where those entries are zero. Replacing only A_nn by 1 changes no earlier pivot, earlier pivot row or column, or earlier multiplier. It increases the positive final pivot, so it preserves nonsingularity. These operations reduce an absolute-value final-pivot bound to the normalized positive-pivot argument without discarding any path or tie.

## Order-three bound

The contradiction p3>3 forces pcd>0 and qef>1 since pcd<=1 and qef<=2. The chosen nonnegative c,e then force d,f>0 and qe,qf>1. The original bounds on A23 and A32 force a<0 and b<0; the bound on A22=q+pab is then violated. All strict inequalities needed by this reasoning follow from the assumed strict violation p3>3, so zero multipliers and ties are covered.

The extension to a possibly singular 3-by-3 matrix is valid when its first two pivots are admissible and nonzero: a nonzero final Schur value permits the same normalization, and a zero final value already satisfies the bound. This is sufficient for the later principal-submatrix argument.

## Scalar inequality

Checked the stated elementary bounds for h(c,d)=3cd+1+|c-d| on the complete domain 0<=c<=1, -1<=d<=1. The sign cases in the lemma are exhaustive: q<=1; q>1 with b>0; a>0>b with d2<=0; d2>0,d1>=0; and d1<0<d2.

In the last case the product bound q*c2*d2<=min(q,U,V,UV/q) follows from c2,d2 in [0,1] and their two linear upper bounds. The function Phi(q,U,V)=2q+2min(q,U,V,UV/q) is nondecreasing in each positive argument. For q>=max(U,V), its derivative in q is 2-2UV/q^2>=0; the preceding two pieces are increasing and meet continuously. Therefore replacing q,U,V by 2,1+c,1+v respectively is legitimate. Nonnegativity of h(c,-v) justifies replacing its multiplier p<=1 by 1. The final expression is exactly 8-2(1-c)(1-v)<=8.

As an independent cross-check of this central inequality, I proved the stronger bound p+q+pc1d1+qc2d2<=4 from the same constraints by a separate bilinear breakpoint argument. Combining it with h(c,d)<=2(1+cd) gives the required bound 8. This alternative derivation is recorded in [the independent scalar proof](scalar-lemma-independent-proof.md) and is not needed to repair the manuscript.

## Order-four bound

The principal submatrix on indices (1,2,4) has initial maximum entry at most 1, has the same first two nonzero pivots, and retains their row-and-column maximum properties upon deleting index 3. Its final Schur value is 1+W; applying the order-three result gives W<=2 even if that submatrix is singular.

When c3*d3<=0, the desired last-pivot bound follows immediately. In the remaining case C=c3,D=d3 are positive and at most 1. Multiplication of the three original-entry inequalities by CD,C,D therefore preserves their directions and produces the displayed bound for 3w3. Relaxing each actual pair (u_i,v_i) to its bilinear minimum on [-1,1]^2 only weakens that upper bound.

Each such bilinear minimum is attained at a corner. Its negative is a maximum of four functions affine separately in C and D. Since p1,p2 are positive, the whole function B is separately convex. Applying the convex endpoint bound first in C and then in D is sufficient to bound it by its four corner values; joint convexity is not required.

The corners (0,0),(1,0),(0,1) are bounded by 6,10,10 respectively using W<=2 and p1+p2<=3. At (1,1), the identity min(uv+du+cv)=-1-|c-d| is valid on the stated complete sign domain: the two opposite-sign corners give this value and the two same-sign corners are no smaller. The lemma applies exactly to the original entries A22,-A24,A42, so B(1,1)<=11. Consequently p4<=1+11/3=14/3.

Earlier active stages have maximum entry at most 1,2,4. Hence the final-pivot calculation establishes the requested full growth bound rather than only a bound on the last diagonal entry.

## Independent exact witnesses

The separate standard-library script [independent_witnesses.py](../independent_witnesses.py) recomputes every active Schur complement using rational arithmetic and checks the rook condition on every selected row and column. It confirms:

- order three: pivots (1,1,3), determinant 3, growth 3;
- order four: pivots (1,1,5/3,14/3), determinant 70/9, growth 14/3.

The initial norms are exactly 1. All pivots are nonzero, and the ties used by the examples are expressly permitted by the canonical statement. No floating-point premise is used to establish the lower bounds.


## Final packaging audit

The canonical mathematical core was compared byte for byte with the preserved reviewed draft after replacing LaTeX inline/display math delimiters with the Markdown-renderer equivalents and removing the two layout-only `\Needspace` lines with their added blank lines. The sole other final layout insertion, `\pagestyle{plain}`, precedes this core. The normalized bodies match exactly: the target definition, Theorem 1, all five proof sections, every equation and both witnesses are unchanged. The final YAML author/affiliation metadata, scope description, exact-script link and contextual reference list were checked against the packaged artifacts. The contextual references are not premises of the self-contained upper-bound proof.

The copied [independent scalar proof](scalar-lemma-independent-proof.md) is byte-identical to the audited independent derivation and was rechecked. Its nine breakpoint values and bounds are correct. In its transpose/sign-relabeling case, if the newly named d2 is zero, the already proved d2<=0 case applies; otherwise the subsequent positive-d2 product bound applies. Thus that boundary is covered. The appendix's closing statement limits its own scope to the scalar lemma; this review separately certifies that the complete order-four reduction has been checked.

The packaged [independent witness checker](../independent_witnesses.py) is byte-identical to the separately written rational verifier used for this review. All paths in this report refer to retained repository artifacts.

No mathematical revision was required by this independent review.

Signed: independent Codex agent `/root/prepare_manuscripts`, 11 September 2026.

## Contact metadata correction (11 September 2026)

At the author's request, the canonical manuscript and preserved agent draft now omit his email while retaining George Stepaniants, his department and university. The coordinating agent checked that deleting the sole contact metadata line from the previously reviewed Markdown produces the current Markdown exactly, and that the generated TeX after `\pagestyle{plain}` is byte-for-byte unchanged. The preserved draft's mathematical text is also byte-for-byte unchanged. The historical hashes above identify the prior reviewed versions; current source SHA-256 is `abe560be8d00a2a98fb4a11619d5e77926649172fbb07828e747500139e97620`, and current preserved-draft SHA-256 is `de3f2323a429b67124097accd23a066633dee2b02f86a75631d60e5551fd6fa2`. All six pages of the regenerated proof PDF were rendered and visually inspected. No mathematical change or new mathematical review is represented by this correction.

## Upstream integration check (11 September 2026)

The canonical entry was reconciled with upstream `main` at `16369809e6e600144bd350ab70b7473b652f46f1`. The complete order-three/order-four resolution and Solved status are retained. Matthew J. Colbrook's related order-five construction, exact rerun, independent review and submission-record links are retained together immediately after the resolution; only the obsolete current-Open sentence was recast as historical scope. The canonical problem statement remains byte-identical to upstream. The mathematical `solution.md`, `solution.tex` and `solution.pdf` are byte-identical to their pre-merge versions, so this integration makes no mathematical revision and requires no new mathematical verdict.

The upstream renderer regenerated only the canonical problem document. Both final pages were rendered and visually inspected: the resolution, attributed related result, original target, references and historical audits are legible, with no clipping, overlap, missing glyphs or reported overfull boxes. This is a scope-preservation and document-QA addendum by Codex agent `/root/review_aa01`, not a replacement of the independent mathematical review above. Current fingerprints and the unchanged proof-file hashes are recorded in `../document-checks.json`.
