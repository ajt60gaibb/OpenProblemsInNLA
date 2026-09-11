# MD-06 independent probabilistic proof review

Review date: 2026-09-11. This review independently checks the complete manuscript, the two supplementary random-graph notes, and the exact hypotheses of the cited primary probability theorems. It does not adopt the package's self-audit labels as evidence. No supplied source or canonical problem was edited.

## Verdict and precise scope

**PASS for the asymptotic proof and the supplementary multiplicity consequence.** Together with the deterministic obstruction established in the manuscript, the random-graph argument proves that the probability that every local minimum is synchronized tends to **zero**, in precisely the canonical uniform labelled simple cubic-graph model. Recommend MD-06 be recorded as resolved negatively, subject to the separately recorded deterministic and finite-certificate reviews. This is the opposite of the proposed limit one.

The stronger uniform positive-cosine and mean-zero Hessian conclusion also follows. The supplementary note proves that the number of nonsynchronized nondegenerate local minima modulo rotation diverges in probability. Its deterministic count is exponential in the number of separated gadgets; **no polynomial or exponential lower bound in n is proved**. No claim about basin sizes, convergence from random initial phases, a useful finite-size threshold, novelty, or author identity is included in this verdict.

The canonical target is `matrix-discrepancy-and-optimization/MD-06/README.md`: n tends to infinity through even integers, the distribution is uniform on all labelled simple 3-regular graphs, and local minima are taken on the phase torus, including nonstrict minima caused by common rotation. A single nonsynchronized local minimum suffices to negate the event quantifying over every local minimum. The manuscript actually produces a strict local minimum after quotienting by common rotation, so its witness meets the canonical definition.

## Complete source identity and coverage

Sources are relative to `.cache/colbrook-package-five/nla_submission_package/`. Each hash is SHA-256 of the complete UTF-8 file with CRLF replaced by LF and no trimming or other normalization.

| File | Normalized bytes | SHA-256 |
|---|---:|---|
| `MD-06/manuscript/md06_counterexample.tex` | 22,850 | `fac30c17d890f6d0f767321ea13e7ff147a867073fef265f00a2ccf88ac66f75` |
| `research_notes/random_graph_inputs_audit.md` | 6,418 | `ed878452e82766414f5033a8bf0c33a3eaef725dcc057906dc7935bdab3abe86` |
| `research_notes/md06_many_minima.md` | 5,617 | `7214eb411cfb72b48626ca867c923d23aec50704697248ea75e150cc07951ca6` |

The entire standalone TeX source was read, not just its random-graph section. The focus of this review is Theorem 1 (`thm:main`, line 68), the probabilistic section (line 308 onward), Lemma 8 (`lem:clean-random`, line 331), the limit-superior argument, and both complete research notes. The deterministic interface was also checked: Lemma 2 (`lem:certificate`, line 109), Lemma 3 (`lem:profile`, line 168), Remark 4 (line 208), Definition 5 (line 228), Proposition 6 (line 239), and Theorem 7 (`thm:deterministic`, line 283). Finite examples and their execution claims are supplementary rather than premises of the probability argument; detailed finite-code verification is assigned to a separate review.

## Deterministic interface used by the probability proof

The small-gradient lemma is valid. On the mean-zero radius rho=c/(2 sqrt(2)) ball, every edge difference moves by at most c/2. Cosine's Lipschitz constant one preserves edge weights at least c/2. The spectral assumption then gives strong convexity with constant c gamma/2. The strict gradient bound makes the radial directional derivative positive on the boundary, so a minimizer on the closed ball is interior and has zero full gradient: the gradient is always mean zero, and stationarity on the mean-zero slice eliminates its remaining part. This yields a torus local minimum, strict modulo rotation. No false full-space strictness is assumed.

The profile equation has a unique solution t_R in (1/2,1), and t_R decreases with R. Thus c_0=sqrt(1-t_4 squared)>0 is uniform over every R>=4. The identity 2a_0+delta_0=2pi supplies exactly the negative root force needed to cancel the outward tree force. The paired-sign cycle pattern requires a length divisible by four and gives one same-sign and one opposite-sign neighbor at every root, including across the cycle closing edge.

For a clean induced radius-R neighborhood, every nonboundary tree vertex has its full cubic degree inside the neighborhood. The only nonzero residual gradient occurs at depth R, where each vertex has one parent of nonzero phase and two neighbors of zero phase. Arbitrary identifications or edges outside the induced neighborhood cannot affect this cancellation, since those exterior phases are zero. The boundary consists of ell times 2^(R-1) vertices and has force magnitude t_R/2^(R-1) at each vertex. Hence the squared gradient norm is exactly ell times t_R squared times 2^(1-R), as claimed.

The radius condition 2^(R-1)>32 ell/(c_0^4 gamma squared) is exactly sufficient for the small-gradient inequality after squaring. On a cross-sign cycle edge, the distance from the phase difference to 2pi times the integers starts above pi/6>1/2. The correction changes that edge difference by less than c_0/2<=1/2, so the corrected point remains nonsynchronized. The constants c_0/2 and c_0 gamma/2 do not depend on ell.

The explicit bound c_0>1/16 also checks: the stated cubic lower bound for arcsine, the upper bound on arcsin(1/16), and t_*>99/100 give the displayed lower bound for F_4(t_*). The rational comparison 151/96>11/7>pi/2 is valid. Thus the universal final margins 1/32 and 1/320 at gamma=1/10 are justified analytically, not inferred from decimal root estimates.

## Primary spectral theorem: exact model and eigenvalue check

[Bordenave, arXiv:1502.04482v4](https://arxiv.org/pdf/1502.04482v4), printed page 2, defines G_d(n) as the simple d-regular graphs on the labelled vertex set {1,...,n}. Theorem 1 uses the uniform distribution on this set, fixed integer d>=3, and n along admissible even-nd sequences. It bounds the actual second adjacency eigenvalue and the absolute bottom eigenvalue by 2 sqrt(d-1)+epsilon with probability tending to one. The source was read directly on 2026-09-11.

For d=3 and epsilon=1/20, the corresponding Laplacian gap is at least 3-2 sqrt(2)-1/20>1/10. The strict scalar inequality follows, for instance, from 2 sqrt(2)<57/20. This proves the manuscript's gap event in the required model.

An important potential ambiguity is resolved by the theorem statement itself. The source's introductory definition of a “nontrivial” eigenvalue excludes absolute value d, which on its own would not establish connectivity. **Theorem 1 explicitly controls the ordered second eigenvalue**, so it rules out a disconnected regular graph's second eigenvalue d on the high-probability event. The manuscript's connectivity consequence is therefore valid. No separate transfer from permutation graphs, random lifts, or a model of independent perfect matchings is required.

## Primary cycle and subgraph theorems: hypotheses checked

[Johnson, arXiv:1112.0704v5](https://arxiv.org/pdf/1112.0704v5), Section 2, printed page 3, explicitly uses the uniform simple regular-graph model and the even-n restriction for odd degree. Proposition 1(a) applies to a specified embedded graph H of minimum degree at least two, with d<=n^(1/3) and e(H)<=2n^(1/10), and bounds its containment probability by c_1(d-1)^e/n^e. Theorem 11, printed page 12, gives total-variation approximation of fixed cycle counts by independent Poisson variables with means (d-1)^k/(2k). These exact statements and model conventions were read on 2026-09-11.

In this application d=3 and every subgraph H is fixed once ell and R are fixed. The numerical size conditions therefore hold for all sufficiently large admissible n, even though that threshold may be enormous. The same observation applies to the cycle-count theorem with fixed maximal length r=ell. Its approximation error tends to zero. In particular the single-cycle count has Poisson mean mu_ell=2^ell/(2ell), and the probability of no such cycle tends to exp(-mu_ell). Total-variation convergence directly justifies this zero-count probability, without any issue about discontinuity of singleton events under general weak convergence.

## Clean fixed neighborhoods: PASS

For any ell-cycle in a cubic graph, the induced radius-R neighborhood has at most ell times 2^R vertices: the cycle contributes ell, and level j>=1 contributes at most ell times 2^(j-1). It is connected and already contains the original cycle. If it is not clean, it has at least two independent cycles, so e-v>=1.

Successively removing leaves preserves e-v. The resulting core is nonempty, has minimum degree at least two and maximum degree at most three, and retains e-v>=1. In particular it satisfies the minimum-degree hypothesis of Johnson's proposition; applying the proposition directly to a tree-containing neighborhood would not have met that hypothesis. The pruning in the manuscript fixes precisely that issue. No isolated final vertex can occur because the original cycle survives the pruning.

For fixed ell,R there are finitely many possible unlabelled core types of bounded size. A type with v vertices and e edges has at most n^v labelled embeddings, and each embedding has probability O_H(n^-e). Summing gives O_H(n^(v-e))=O_H(n^-1). Summing over all the fixed types remains O_(ell,R)(n^-1). This bounds the probability of **any** dirty ell-cycle neighborhood in the graph; it is not merely a conditional statement about a preselected cycle. No extra union bound over all cycles is missing.

For the multiplicity note, if two distinct ell-cycles have intersecting radius-R neighborhoods, their distance is at most 2R. Their union, together with a shortest connecting path if needed, is a bounded connected subgraph with at least two independent cycles. If the cycles intersect, they are still distinct cycles and have cycle-space rank at least two. After any necessary pruning the same fixed-core argument applies. Thus the probability of any such pair is O_(ell,R)(n^-1). Chords, overlapping cycles, and cycles sharing a path are covered by the excess argument; no disjoint-cycle assumption is silently imposed at this stage.

## Configuration-model note: conditioning and factorial moments

The main proof already has direct simple-model theorems, so the supplementary configuration-model derivation is not a hidden prerequisite. Its claims nonetheless check independently.

A prescribed set of e disjoint pairs of half-edges in a uniform perfect matching of 3n half-edges has probability equal to the reciprocal product (3n-1)(3n-3)...(3n-2e+1). For fixed e this is O(n^-e). A given labelled simple cubic graph has exactly (3!)^n preimages, obtained by assigning its three distinct incident edges to the three half-edges at each vertex. Conditioning on simplicity therefore gives the desired uniform labelled model, not a distribution weighted by unlabelled automorphism classes.

The expected k-cycle count uses (n)_k/(2k) vertex cycles and 6 choices of two ordered half-edges at each vertex, giving mean tending to 2^k/(2k). For loops the mean tends to one; for double edges it also tends to one. Counting unordered pairs of parallel edges makes the absence of loops and double-edge pairs exactly equivalent to simplicity, since triple edges contain such pairs.

In every fixed mixed factorial moment, vertex-disjoint cycle patterns give the product of the limiting means. Distinct overlapping cycles form a multigraph component with e-v>=1, hence contribute O(n^-1) by the prescribed-pair bound and the finite number of bounded half-edge types. Repeated copies of the same cycle are excluded by the factorial moment. Impossible overlaps using too many half-edges contribute zero. The standard factorial-moment characterization therefore gives the joint independent Poisson limit, including lengths one and two.

The simplicity probability consequently tends to exp(-2)>0. Integer-valued joint counts permit convergence of each finite joint point probability using half-integer continuity boxes. Conditioning on the zero loop and zero double-edge counts leaves the limiting higher-cycle law unchanged. Similarly, fixed-subgraph containment expectations O_H(n^(v-e)) remain of that order after conditioning, since the conditioning probability stays bounded below. These steps justify the note's simple-labelled transfer and do not confuse the configuration model with a superposition of random perfect matchings.

## Main limiting quantifiers: PASS

Let S_n be the canonical event that every local minimum is synchronized. Fix any multiple of four ell and choose a finite R satisfying the deterministic condition at gamma=1/10. If the graph has the required gap, has an ell-cycle, and has no dirty ell-cycle neighborhood, then S_n is false. Thus

\[
\Pr(S_n)\le\Pr(\lambda_2(L)<1/10)
 +O_{\ell,R}(n^{-1})+\Pr(C_\ell=0).
\]

This uses only a union bound. Independence of expansion, cycle counts, and cleanliness is neither assumed nor required. First taking the even-n limit superior yields the bound exp(-2^ell/(2ell)) for **each fixed** ell. To make the quantifiers explicit, given epsilon>0 choose one multiple of four ell with this expression below epsilon, then choose its finite R, and only then take n sufficiently large. This proves limsup Pr(S_n)<=epsilon for every epsilon>0 and hence the claimed limit zero. There is no unjustified interchange of limits or use of a fixed-length theorem with an n-dependent cycle length.

The same bad-event bound applies to failure to obtain a nonsynchronized minimum with the stated uniform cosine and Hessian margins, because c_0 is independent of ell and R. This validates the stronger assertion of Theorem 1. Disconnected graphs do not create a loophole: the high-probability spectral event ensures connectedness; their complementary probability is included in the bound.

## Multiplicity note: deterministic separation and probability limit

For m cycles with clean pairwise vertex-disjoint radius-R neighborhoods, each profile has nonzero phases strictly inside its neighborhood and gradient only on its depth-R boundary. No edge joins distinct nonzero supports: such an edge would place a vertex in both radius-R neighborhoods. Nor can a boundary vertex receive a force from the nonzero support of another profile without the same forbidden intersection. Edges between two zero-phase boundaries have zero force. Consequently active profiles can be summed without creating mixed nonlinear interactions, and their residual gradient supports are disjoint.

For every active subset A, the squared gradient norm is |A| ell t_R squared 2^(1-R), bounded by the m-profile quantity. Taking c=1/16 and the note's strengthened radius inequality makes the small-gradient lemma applicable to all 2^m subsets. This is a finite deterministic family of existence applications, not a probabilistic independence assertion about the corrections.

On a chosen cross-sign core edge, an active profile leaves phase distance from 2pi times the integers greater than 15/32 after correction, whereas an inactive profile leaves distance less than 1/32. These disjoint intervals recover every bit of A. Edge differences are invariant under common rotation, so the resulting minima are distinct even modulo rotation. Nonempty subsets are nonsynchronized. The uniform margins are 1/32 for edge cosines and gamma/32 for the mean-zero Hessian. This proves N(G)>=2^m-1 under the deterministic hypotheses.

For the random-graph consequence, fix m first, then ell and R. The same gap, cleanliness, and pair-separation bounds reduce the failure probability to Pr(Poisson(mu_ell)<m) in the n-limit superior. Letting the fixed multiple of four ell increase afterwards drives this tail to zero. Therefore, for every fixed m, Pr(N(G_n)>=2^m-1) tends to one. This is exactly divergence in probability and does not supply a rate in n. The note explicitly retains that limit, and the packaging should do so too.

## Canonical source, prior scope, and archive limitations

[Randomstrasse101, arXiv:2504.20539v1](https://arxiv.org/html/2504.20539v1), Definition 2.1 and Conjecture 3, was read on 2026-09-11. The energy normalization agrees with the manuscript for an undirected graph. Its angular parametrization supports the canonical torus formulation; the isolated sphere notation in its definition is not an extra constraint on this canonical problem. The manuscript answers the recorded random cubic-graph assertion, not the high-degree or dense-graph results cited nearby.

[DeVille and Ermentrout, arXiv:1512.06140](https://arxiv.org/html/1512.06140), Sections II.1, III.7, and IV, was also inspected. It studies finite stable patterns and explicitly describes data suggesting that the fraction without a pattern tends to zero. The submission's acknowledgement is accurate. Those observations are precedent for the phenomenon, not themselves the precise asymptotic theorem proved here. This bounded source comparison does not establish priority of the proof.

The actual archive includes the main TeX/PDF, two rational finite certificates, their verifier, and the research notes, but omits several supplementary programs and outputs mentioned in its prose, including `analytic_gadget.py`. This review therefore does not certify claims that those absent programs were run or that their described test outputs were supplied. The analytic random-graph proof does not invoke those absent artifacts, so this documentary limitation does not create a gap in Theorem 1 or the multiplicity consequence. Finite-certificate execution evidence is recorded separately.

No substantive probabilistic gap was found. Exact primary-theorem hypotheses, labelled simplicity, fixed-parameter counting, connectivity, and the order of limits all support the stated negative resolution.
