# NR-04: independent mathematical review

Reviewer: independent agent `/root/review_transfer_counterexamples`, 2026-09-11.

**Verdict: PASS. The manuscript supplies a complete exact resolution of canonical NR-04: `rank_+(D_9)=7`, so a real nonnegative six-term factorization does not exist.** The geometric lower bound and integer upper certificate both check out. No substantive gap or untreated exceptional configuration was found.

## Reviewed material and immutable identity

Read the entire original `.cache/colbrook-all-submission/nla_submission/manuscripts/NR-04_nine_point_distance.tex`, including the local preamble and all proofs, the canonical `nonnegative-and-positive-factorizations/NR-04/README.md`, and the diagnostic `verification/verify_nr04.py`. The original manuscript has no external preamble dependency. No proof or canonical file was changed.

SHA-256 of the **full** UTF-8 source after CRLF-to-LF normalization, with no trimming of whitespace or final newlines:

`af80f8fcbf60110891065c58ef5433a3b945c3c9e6476d9126fecfef2e5cc85c`

Normalized length: **8970 bytes**. The extracted original already used LF.

### Reviewed revision: bibliography locator and explicit convexity

At the parent agent's request, made exactly three substitutions in `references/colbrook-factorization-2026-09-11/reviewed-sources/NR-04_nine_point_distance.tex`:

- `Sections 3.2--3.3 and Theorem 8.` → `Section 4.2.1 and Theorem 8.` in the bibliography;
- `bounded two-dimensional polygon.` → `bounded two-dimensional convex polygon.` in the contact lemma;
- `Every polygon $R$ satisfying` → `Every convex polygon $R$ satisfying` in the same lemma.

The two added “convex” words make explicit the hypotheses used by the lemma's normal-cone argument. In its application, `P=L intersect R_+^N` is convex and `R=T intersect L` is convex because `T` is a convex hull. Both remain two-dimensional and bounded by the unchanged argument. Thus the revised standalone lemma has the correct scope and every application meets its hypotheses; no downstream proof change is needed.

The original archive and original extracted manuscript remain untouched. A full normalized-text equality check verified that the final revised text equals the original after exactly these three substitutions, with no other differences. The intermediate bibliography-only revision had SHA-256 `81d0fe861ca57062292544cd801e5dfc10185f02c79e1e9ca77ef73e3f49e42f` and length 8966 bytes; it is superseded by the final revision below.

Revised complete UTF-8/LF source SHA-256, again without trimming:

`d06e1f7f30b3f70b0f86edf5dc1bf921d127d11d94aac5a3c0590b1947aa63d7`

Final revised normalized length: **8980 bytes**. **PASS applies to this final revised source; the original main proof also passes with its contact lemma read in the convex setting used by its application.** The corrected locator was checked against the primary source described below.

## Canonical and primary-source alignment

Theorem 1 (`thm:main`, source line 22) uses exactly the canonical nine-by-nine matrix `D_ij=(i-j)^2`, with exact real nonnegative rank. The lower bound applies to every real nonnegative factorization, without imposing rationality, symmetry, stochasticity before rescaling, or equality between a factor's rank and the product's rank. Its conclusion therefore answers the canonical six-versus-seven question in full.

I checked [Baeckelant–Vandaele–Gillis v2](https://arxiv.org/html/2605.14058v2), Appendix A.1 Table 6 and its final paragraph: the recorded gap for order nine is 6/7. That source credits the reflection upper bounds to Hrubeš. I also checked [Gillis–Glineur, *On the Geometric Interpretation of the Nonnegative Rank*](https://arxiv.org/html/1009.0880), Theorem 8 and the surrounding section: it concerns restricted nonnegative rank for rank-three matrices with the stated sparsity property. The new proof reconstructs the needed contact geometry and uses both factors to reach unrestricted nonnegative rank, rather than silently identifying these two notions.

Bibliographic detail: Theorem 8 is in **§4.2.1** of the inspected Gillis–Glineur text. The original manuscript bibliography instead names §§3.2–3.3, which concern the general section method. The reviewed revision corrects this section locator as recorded above. Attribution of the known reflection upper bound should be checked against the benchmark's Hrubeš credit before publication. Neither detail affects the self-contained proof or exact certificate.

## Geometric proof audit

### Contact lemma — Lemma 2, `lem:contact`, lines 32–45

PASS in the convex-polygon setting used throughout the proof. Distinct edges of a convex polygon have distinct outward normal directions. At each such direction the supporting value of `R` equals that of `P`: the inclusion gives one inequality, and the required contact point gives equality.

The vertex normal cones of a full-dimensional convex polygon form a complete cyclic fan. Making their arcs half-open assigns every edge-normal direction to one vertex, including directions where an entire edge maximizes. If two distinct normals are assigned to the same vertex, at least one is in the interior of that vertex's arc, since only one endpoint is retained. For the interior normal the maximizer is unique, so the corresponding `p_i` equals that vertex. The second normal puts the same vertex on the other supporting line of `P`, contradicting that `p_i` is in the relative interior of a distinct edge. Thus the assignment is injective and `R` needs at least as many vertices as contacts.

This handles the important degeneracy in which a supporting line exposes an edge of `R` rather than a unique vertex. Treating every support direction as having a unique maximizer would have been a gap; the actual half-open-arc argument avoids it.

Terminology clarification applied in the reviewed revision: the original lemma statement says “polygon” without explicitly adding “convex.” Its normal-cone proof uses convexity. The final revised statement explicitly requires convexity of both polygons. In its sole application, `P` is an affine-plane intersection with an orthant and `R` is an affine-plane section of a convex hull, so both meet this requirement. This corrects the standalone lemma's scope while preserving the main theorem and its proof.

### Small section from a low-rank factor — Lemma 3, `lem:factor`, lines 48–71

PASS. The following checks cover its normalization, dimension, contact, and section-count steps.

1. Zero columns of `W` may be removed together with their coefficient rows. Every remaining nonnegative column has strictly positive sum. All columns of `M` have strictly positive sums, because rank three implies at least three indices and every off-diagonal entry is positive. The proposed divisions are therefore legal. Scaling nonzero columns by positive numbers, and compensating in the other factor, preserves the product and the needed ordinary ranks. Removing a zero column preserves the rank of `W`.
2. After the two rescalings, `X=UV` and columns of `U` and `X` sum to one. Then `1^T X=1^T U V` implies columns of `V` sum to one as well. The columns of `X` are convex combinations of columns of `U`, not merely conic combinations.
3. A nonempty set of vectors with coordinate sum one has affine dimension equal to its linear rank minus one. Thus `dim T=rank U-1<=3` and `dim L=rank X-1=2`. Since the columns of `X` lie in `T`, `L` lies in `aff T` and dimensions zero and one for `T` are impossible. This exhausts the cases before the two-/three-dimensional split.
4. Every point of `L` has coordinate sum one, so `P=L intersect R_+^N` is contained in the standard simplex and is bounded. Both `P` and `R=T intersect L` contain the two-dimensional convex hull of the columns of `X`; they are full-dimensional within `L`, nonempty, bounded convex polygons.
5. At column `X_:j`, precisely coordinate `j` vanishes. All the other coordinate inequalities are strict there. Coordinate `j` is nonconstant on `L`, because it is positive at the other columns. Locally its zero set is a line in `L`, and the strict remaining inequalities leave a segment on that line and a one-sided neighborhood. Hence the point lies in the relative interior of an actual edge of `P`, not an isolated vertex or a redundant inequality's empty face. Distinct indices give distinct edges: another column has coordinate `j` strictly positive and cannot be on that edge.
6. The contact lemma now gives `N<=number of vertices(R)`. This is the necessary restriction arising from the exact zero pattern; symmetry is not used.
7. If `dim T=2`, then `aff T=L`, so `R=T` has at most the six supplied generating points as vertices. Repeated generators and nonextreme generators only decrease the vertex count.
8. If `dim T=3`, let `v<=6` be its actual vertex count. A three-dimensional convex polytope satisfies `e<=3v-6` and Euler's relation `v-e+f=2`, hence `f<=2v-4<=8`. This applies to nonsimplicial facets too; triangulation is not assumed.
9. A facet halfspace description in `aff T` restricts to at most eight halfplane inequalities on `L`. Restrictions may become redundant, identically true, or identical; these do not increase the number of edges. The section contains a two-dimensional set, so no problematic empty or one-dimensional section occurs. Even if the plane contains a polytope edge, a vertex, or an entire facet, it remains described by at most eight halfplanes and has at most eight edges and vertices. General position is unnecessary.

Combining these cases gives `N<=8`, exactly as stated. It is legitimate to use the coarse facet count without claiming it is the largest attainable section size.

### Both factors and Sylvester — Theorem 4, `thm:general`, lines 73–81

PASS. Assume an inner dimension `k<=6` for a matrix of order `N>=9`. By Lemma 3, the left factor must have rank at least five. Apply the same lemma to `M^T=H^T W^T`; the transpose also has ordinary rank three, zero diagonal, and strictly positive off-diagonal entries. It follows that the right factor must have rank at least five. Sylvester's inequality gives

`rank(WH)>=rank W+rank H-k>=5+5-6=4`,

contradicting rank three. When `k<5`, the rank-at-least-five conclusion is already impossible; the displayed inequality remains a valid contradiction under the same hypothetical assumptions. Thus smaller inner dimensions are not omitted. The conclusion is unrestricted nonnegative rank at least seven, not just restricted nonnegative rank. Nonsymmetry causes no obstruction.

## Exact upper certificate and ordinary rank — §5, lines 85–106

PASS. Expanding `(i-j)^2=i^2+j^2-2ij` gives rank at most three. The leading three-by-three determinant is **8**, so the rank is exactly three. The diagonal is zero and all off-diagonal entries are strictly positive, satisfying Theorem 4.

The first five columns of `W` select the unique value `|t_i|` among `0,...,4`. Their product with the first five rows of `H` gives precisely `(|t_i|-|t_j|)^2`. The last two terms add `4|t_i t_j|` when `t_i,t_j` have opposite signs and zero when they have the same sign or either is zero. In both cases the result equals `(t_i-t_j)^2`. Since `t_i=i-5`, this is the required matrix entry.

All factor entries are nonnegative integers. The center `t_i=0`, both boundary values ±4, identical indices, opposite reflected pairs, and same-sign pairs are covered by this identity. The factor dimensions are exactly nine-by-seven and seven-by-nine. Thus the upper bound seven is fully constructive and exact.

## Independent computation and checker coverage

A separate Python standard-library `fractions.Fraction` implementation, without importing or executing the submitted checker, verified the matrix rank, determinant 8, all 81 entries of `WH=D`, integrality and nonnegativity, and the factor ranks. The explicit upper factors have ordinary ranks **6 and 4**; Sylvester gives `6+4-7=3`, consistent with their product. They do not contradict Lemma 3, whose inner-dimension bound is six.

For inner dimension six, the ordinary-rank pairs allowed just by rank-three product and Sylvester are

`(3,3), (3,4), (3,5), (3,6), (4,3), (4,4), (4,5), (5,3), (5,4), (6,3)`.

Every pair has a factor of rank at most four, exactly the obstruction the geometric lemma supplies. I read the submitted diagnostic and confirmed that it checks this arithmetic and the upper certificate, while correctly declining to treat numerical tests as a proof of its geometric lower bound. The lower bound was reviewed analytically above.

## Scope, remaining cases, and disposition

- **Canonical NR-04:** no mathematical cases remain. If this candidate is accepted, the exact answer is seven and no six-term real nonnegative factorization exists.
- The more general lower bound for any order `N>=9` and rank-three matrix with one zero per row/column in diagonal position is proved. It includes nine-point linear distance matrices with any distinct real coordinates, since these have rank three. The integer seven-term construction, however, concerns the equally spaced nine-point instance only.
- No exact rank formula for arbitrary coordinates or for all larger distance matrices is supplied, and coincident coordinates or extra zero off-diagonal entries fall outside the general lower-bound theorem. These are not outstanding cases of canonical NR-04.
- The proof is an independently reviewed candidate. Novelty against every later source, priority, formal verification, and publication acceptance remain separate matters. The convexity and section-locator clarifications recorded above have been incorporated in the final reviewed source and do not alter the canonical mathematical conclusion.
