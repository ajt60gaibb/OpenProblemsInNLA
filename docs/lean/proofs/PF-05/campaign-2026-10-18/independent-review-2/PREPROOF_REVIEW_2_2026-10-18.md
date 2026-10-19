# PF-05 fresh independent preproof statement and route review

Date: 2026-10-18. Reviewer: `/root/fr05_statement` (AI agent).

**Decision: APPROVE the unchanged exact PF-05 mathematical statement and frozen Lean boundary for continued proof implementation. The retained seven-module candidate is partial, and neither the full target nor its positive-entry case is proved by that candidate.** No new mathematical proof bodies were written in this review. All writes are confined to this external review directory; canonical pages, originals, the old checkout and shared dependency caches remain untouched.

## Exact reviewed inputs and boundary

The complete input inventory, candidate Git blobs, immutable snapshots, dependency revisions and SHA-256 hashes are in `input-lock.json`. Candidate commit: `6e2c960557b6f61af1ed6e679b0634dd498181b2`. Its seven proof modules were read from Git objects, not modified in an old worktree.

| Input | SHA-256 |
| --- | --- |
| Canonical PF-05 README and complete ORIGINAL.md, byte-identical | f7acc0629067696f7aa2828673740e286730fb9654348b742752eb146a840f71 |
| Exact numerical specification | d5c00daa8a0bfa9b520c999b017217ab07fe9bb76b2cac6240f12f241b5db184 |
| Shared live PF05 statement | 3ac9a2fb395d96c3b61c6f2593144caac010da4bfafd2d96f86627aa7a75859d |
| Frozen Reviewed/PF05 statement | df79daee68563e5bb6a6d85cf70246bf2154f12bcc5fe5a6a806e8009e558b7f |
| Published standalone Colbrook proof TeX | fab2b46fb396aea58744c5b90bb5795b95e7c84819a62d73d31e54dbd5d784d6 |
| Reviewed-source and original submitted TeX, byte-identical | dafb9c110fefe4e0803649714c1b323f62bfae1670926ec7ab65153ad20c459e |

The target universally quantifies finite real p-by-q matrices, explicit entrywise nonnegativity, ordinary rank exactly three, PSD rank exactly two, and every fixed size-two PSD factorization. The PSD-rank clause means existence at two and absence at one, matching the source's positive-size minimum. Ordinary rank three excludes empty dimensions without a new dimension restriction. The actual real PSD predicate is symmetry plus a nonnegative full quadratic form, and the trace is the ordinary trace of the ordinary matrix product.

Every symmetric direction family is quantified. The displayed trace derivative must vanish for every pair, and one common `h > 0` must keep all actual straight segments PSD for every real `0 ≤ t < h`. This does not require the positive-time tuple to factor M and does not replace actual straight feasibility with the weaker tangent-cone condition. Rigidity is exactly one common scalar `d` with `E_i=d A_i`, `F_j=-d B_j`. Uniqueness quantifies every alternative size-two PSD factorization and one common real S with nonzero determinant and precisely `Atilde=Sᵀ A S`, `Btilde=S⁻¹ B (S⁻¹)ᵀ`. The determinant guard makes the total Mathlib inverse a genuine inverse. Both implications, all zero entries, zero rows/columns, singular/repeated factors and all p,q are retained.

The candidate's local statement copies match the shared live/frozen/infrastructure bytes. `Check.lean` proves live/frozen equality by reflexivity. Its Comparator selects only `NLA.PF05.target`, permits only the standard three axioms, and has no definition holes. `Challenge.lean` contains exactly the intentional target hole, and no `Solution.lean` exists in the candidate. Earlier approvals are historical evidence; this review independently rechecks the current exact bytes.

## What the seven retained modules actually prove

| Module | SHA-256 | Actual reusable result |
| --- | --- | --- |
| Basic | ed1077fe63c84a5c958b14a4265f68307d67fc67135e2272f2619ec326df77a1 | Actual PSD bridge/2-by-2 criterion, trace-pairing nondegeneracy, rank-three coordinate spanning, zero-row/column factor and direction vanishing, zero-trace PSD product zero and singularity. |
| Congruence | 2e5899f22fcfe722b03eb73a6ed50e5d4778fdb3f82ca7c464fd1ba36fda7047 | Exact primal/dual congruence, PSD/symmetry/trace preservation, factorization and actual straight-feasible-direction transport. |
| Operator | e5e6dd822bb04e2363aabbcf2dea1578b951343208ed072356fdc5f52b923a83 | Actual invertible 3-by-3 coordinate change between two factorizations of the same rank-three M, with the actual inverse dual action. |
| ZeroPair | e4a21b1af8026ab97492309a260a44aa0ce8ff2c9a8356d8e3dbdf5022223929 | Actual nonzero orthogonal-pair coordinate identities in either positive-diagonal case. |
| ZeroNormalize | 736d6d03d70ef1de5ed77aa57e1933b5a67435366392e532c10454f936b781b8 | An actual invertible shared congruence normalizing a nonzero zero-trace pair to P=diag(1,0), Q=diag(0,1). |
| PositiveReduction | e6cbcbb308035d5481cf11855ebac95c5070120bdc81372e2c39e096ebfde31e | Actual finite positive-ray quotient compression, rank-three and both-property transfer, and conversion of distinct singular outer-product rays to independent generators. It already constructs the compression; its earlier interim comment must not be mistaken for a remaining construction gap. |
| PositiveTopology | 86b99ca504a8a20ffbc03d01a56f6f2637b5fb07d0a56d7038f1b82ef8b461c3 | Actual positive-definite aggregate sums and invertibility of an already existing limiting row-congruence matrix into a valid rank-three factorization. It does not construct that limit or prove orbit closedness. |

No support module exports the full Target. In particular, `Operator` supplies the finite change L, not the still-missing infinitesimal direction operator T or its integration. `PositiveTopology` is an initial algebraic/coercivity ingredient, not a completed topological proof.

The coordinate convention is asymmetric and exact: primal rows use `(a,c,b)` and dual columns use `(d,f,2e)`, so their dot product is `ad+cf+2be`. Future adjoint/inverse-adjoint lemmas must retain this weight and ordering. A Euclidean transpose of an unweighted `(a,b,c)` coordinate matrix would be wrong.

## Essential source check and genuine positive/topological gap

The full retained Colbrook proof, including its integration, scalar-line, normalization and explicit zero-case construction, was read. Its symbolic checks are supplementary algebra diagnostics; they do not establish a universal Lean theorem. The zero-case algebra has a concrete formalization route, with no new statement restriction justified by the manuscript.

The [official Dawson–Hoşten–Kubjas–Metsälampi v2](https://arxiv.org/html/2410.18891v2), dated 31 August 2026, was checked at Definition 1/Remark 1, Theorems 4.1, 5.1, 5.2, Lemma 19 and Proposition 7. Its size-two second-order convention matches actual straight-segment PSD. Theorem 5.2 supplies the positive-entry equivalence cited by the local manuscript. Its proof uses additional infinitesimal/local/global steps; the distinct rank-one-ray hypotheses occurring in Theorem 4.1 require a real reduction, which the candidate's positive-ray compression supplies. The primary local argument also uses an analytic-path/curve-selection step. No corresponding complete formal theorem is supplied by the candidate, and the external theorem cannot be imported as an axiom.

**Independent topological inference:** an isolated point of a connected quotient need not be its only point unless that point is also closed. Thus the inference used in the cited Lemma 19 needs, for this formal route, an actual closed-orbit/T1 argument (or a different valid direct argument). This observation is a missing proof gate, not a counterexample to PF-05. The candidate only proves that a proposed limiting S is invertible. Before using it, one must prove boundedness and extract a convergent congruence subsequence, pass the row congruences to the limit, then pass the inverse dual congruences. Connectedness of the actual factorization quotient is a further theorem, not a consequence of this orbit-limit calculation.

A plausible properness route from the existing aggregate lemma is quantitative: let P be the positive-definite sum of the original row factors. If `S_nᵀ P S_n` converges, positivity of P bounds all columns of S_n. Finite-dimensional compactness gives a subsequence; the already-proved rank-three limit lemma makes its limit invertible; inverse continuity then recovers both factor families. This would prove relative orbit closedness. It still does not establish quotient connectedness or infinitesimal-to-local rigidity. I do not assume any of those missing results.

## Exact remaining theorem obligations

1. **General reverse implication:** for any actual rank-three size-two factorization, prove `UniqueUpToCongruence M A B → InfinitesimallyRigid A B`. Construct the unique linear T representing a feasible direction, with `E=T A`, `F=-T* B` under the actual trace pairing. Integrate by `A(t)=(I+tT)A`, `B(t)=(I+tT*)⁻¹ B`. At a rank-one dual factor, positive inward coefficient permits a determinant derivative argument; zero coefficient must force the off-diagonal perturbation to vanish and give an exact eigenvector formula. Continuity alone cannot handle that flat case. Choose one common interval for the finite families. Under uniqueness, spanning makes every `I+tT` an actual congruence operator; prove that an entire such affine line forces T to be scalar.

2. **Zero-pair forward implication:** assume actual indices i,j with `A_i≠0`, `B_j≠0`, `trace(A_i B_j)=0`. Normalize both the given and alternative factorizations, derive the actual shear/reflection normal form `L(a,b,c)=(a+αb+βc,γb,c)`, `γ>0`, and its weighted inverse-adjoint formula. Inequivalence must imply `(α,β,γ)≠(0,0,1)` after those actual congruences. Construct `σ=γ²−1`, `E(A)=(-σa+αb+βc)P`, `F(B)=d[[σ,-α/2],[-α/2,-β]]`. Prove the actual trace equations and a common PSD straight interval for every PSD input factor. In particular the dual zero-leading-coefficient case requires the exact square identity and scalar eigenvector reduction, not merely a tangent inequality. Spanning must show the resulting direction fails the frozen common-scalar condition.

3. **Zero rows/columns and congruence wrappers:** Basic already forces those factors and feasible directions to vanish, but actual restriction/extension of factorization families, preservation of ordinary rank three, and equivalence of both properties across deletion remain to be packaged. A raw zero matrix entry does not imply a usable nonzero orthogonal pair: it may arise from a zero row or column. In the complementary case all entries on the actual nonzero supports are positive; this is the exact positive core to which a positive-entry theorem may be applied. Congruence composition/inverse and full property-invariance wrappers must also be proved from the existing transport gate.

4. **Positive-entry forward implication:** prove `InfinitesimallyRigid A B → UniqueUpToCongruence M A B` for every strictly positive M in the exact rank-three size-two domain. Existing ray compression removes repeated rays and preserves the properties. The main rigidity theorem on the resulting distinct-ray families remains absent. A route using infinitesimal/local rigidity, closed orbits and connected quotient must prove all those statements; a route using explicit alternatives must provide an actual nonscalar feasible direction. Leaving an external positive theorem, quotient-connectedness oracle, local-global implication or curve-selection oracle as a hypothesis would not complete Target.

5. **Full assembly:** split only on the actual nonzero-pair/positive-core cases, restore all removed zeros and actual congruences, and combine both implications under the unchanged Target. PSDRankTwo may be logically redundant given rank three and the fixed size-two factorization, but it must remain in the frozen target. No status promotion or Comparator success can precede an actual complete Solution.

These are substantial remaining obligations. The shortest self-contained first proof gate appears to be the normalized explicit zero-pair construction, while a separate analytic branch develops integration and a separate geometric branch proves the positive-entry case. This is a proposed work division, not an assertion that the remaining positive theorem is routine or already formalized.

## Pinned API feasibility and limits

Verified existing local APIs include the seven modules above; Mathlib `LinearMap.exists_antilipschitzWith` and `LinearMap.injective_iff_antilipschitz` for injective finite-dimensional maps; `IsCompact.tendsto_subseq` for compact subsequence extraction; `IsClopen.eq_univ` for the correctly closed-and-open connectedness argument; and `hasFDerivAt_ringInverse`/`hasStrictFDerivAt_ringInverse` for normed-algebra inversion at actual units. Their exact pinned source hashes are in the lock. A matrix-inverse bridge and all unit/nonzero-determinant guards would still need proof. A search found no ready `Semialgebraic`, `CurveSelection` or `Ominimal` module in the pinned Mathlib filename inventory; no such API is assumed. Finite sums, determinant polynomials, the actual 2-by-2 PSD criterion, or a local slice may provide alternate concrete routes, but those are unproved proposals here.

## Fresh reproducible evidence

Lean 4.33.1 and all ten actual dependency revisions match the candidate manifest, including Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. The live/frozen/infrastructure candidate copies equal the shared bytes. A private replay freshly compiled those three modules, the unchanged Challenge/Check packet and all seven support modules: twelve source builds passed. A separate generated consumer successfully asserts LeanCert kernel trust and prints the closure of all 114 public support declarations; all closures use only `[propext, Classical.choice, Quot.sound]`. The intentional Challenge is separately rejected by a kernel assertion with `sorryAx`, as required. There is still no Solution and no full Target proof.

`build-result.json` retains the exact commands, hashes, outputs and pin checks. One initial consumer-name collector mistook a prose comment word for a constant; that harness-only failure and its source/log are retained, and the corrected comment-stripping consumer passes. No candidate proof source changed. The source snapshots are exact Git-object copies, not new proof implementation. Input hashes were rechecked after the review. This is local statement/support/preproof evidence, not Linux CI or Comparator verification of PF-05.

Permanent ID **PF-05**, its canonical README path, complete original target and source artifacts are preserved. This approval does not turn any unproved gate into a premise allowed in the final theorem.
