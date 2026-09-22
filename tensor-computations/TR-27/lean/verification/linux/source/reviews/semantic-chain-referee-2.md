# TR-27 generic semantic-chain referee 2

Verdict: **APPROVE the bounded generic semantic chain below.** No mathematical or statement-correspondence change is requested. This is not a full TR-27 package verdict or status-promotion authorization.

Reviewer: AI agent `/root/reference_review`. I independently read all five proof modules and their frozen definitions/statements. I authored none of Semantics, SegreSemantics, AffineBorder, ProjectiveGeometry or CoordinateTransport, and none imports a concrete proof module I authored. I did author IntegralImage, Geometry and BorderWitness elsewhere in this package. I therefore cannot count as an independent final full-package proof referee, and this report supplies no self-review approval for those concrete modules. My earlier statement-only referee report preceded my proof authorship.

## Exact statement correspondence

The ten frozen Challenge declarations implemented by this chain are `finite_coordinates`, `tensor_representatives`, `cone_projective_membership`, `projective_cone_rank`, `rank_minima`, `segre_cone_rank`, `segre_rank_minimum`, `projective_affine_border`, `admissible_geometry` and `coordinate_transport`. All ten source signatures are identical to the frozen Challenge after whitespace normalization; retained `signature-check.json` records that supplementary check. I also reviewed their mathematical content and all 31 other public supporting declarations, not only their names or signatures. No new rank, closure, nonzero-coordinate or answer hypothesis is introduced.

The full mathematical boundary remains the previously independently approved Definitions / Challenge / NUMERICAL_TARGETS. No frozen mathematical file changed during this review. The scope is the exact classical complex projective variety and separate-factor tensor definitions in those files, not a restriction to the concrete curve, finite parameters or a chosen output chart.

## Referee analysis

**Ambient spaces and representative choices.** Finite coordinates use the actual finite-dimensional basis equivalence, including the zero-dimensional case. The generic algebraic arguments quantify over arbitrary complex modules; their finite coordinate presentation is an explicit linear equivalence, not an assumed dimension of twelve. Projective representative equality is proved through actual Mathlib projectivization, with nonzero scale factors. Cone membership is preserved under every scalar (the `cone_smul` statement even includes zero), and the reverse equivalence is invoked only for nonzero scales. Span is related to the linear span of chosen representatives in both directions. Nonzero pure tensors are proved by dual functionals on the two separate factors, and unique projective representation follows from equality with `mk`.

**Rank minima and zero entries.** Cone/projective rank equivalence permits unrestricted complex coefficients, repeated points, arbitrary finite lengths and zero summands. The reverse construction replaces zero vectors by a proved nonzero cone point solely to define a projective list, and proves span membership without treating the replacement as the original summand. Empty lengths are retained. Full cone span supplies an actual finite decomposition for every representative; monotonicity and explicit nonemptiness then justify `csInf_mem`. The same proof supplies nonempty border-length sets from ordinary rank points and closure inclusion. Thus neither rank nor border rank relies on the default infimum of an empty set.

**Segre semantics.** `segrePoints` remains the full image of independently selected left and right projective points in the ordinary tensor product. The forward construction extracts independent x/y families and absorbs their representative scalars into the unrestricted coefficients. The reverse construction separately tests zero tensor terms and fills them with an actual nonzero pure tensor from the cone. It does not identify the two factors or impose symmetric decompositions. The tensor spanning proof uses the bilinear image of two spanning cones, and `segre_rank_minimum` proves nonemptiness before applying the minimum lemma.

**All-polynomial affine/projective closure.** The forward bridge decomposes an arbitrary vanishing polynomial into all its homogeneous components. Scalar closure of the full affine rank set, for every complex scalar, implies each component vanishes: a univariate polynomial identity over infinite ℂ isolates every coefficient. Components above total degree are explicitly zero. The reverse bridge does not assume homogeneous equations vanish at the origin. Instead it chooses a nonzero coordinate of the nonzero target v and multiplies an arbitrary homogeneous equation f by that coordinate variable. This product vanishes at the origin and at every nonzero rank point, so affine closure forces the target evaluation of f to vanish. This handles degree-zero equations and r=0 without an unstated positive-degree or nonempty-projective-rank-set assumption. No Euclidean closure is substituted.

**Closedness, irreducibility and span.** Projective closedness is proved using every homogeneous component of every ideal member. A homogeneous equation vanishing on the projective point set vanishes on the entire affine cone, including its origin: the degree-zero case uses an actual nonzero cone point rather than `0^d=0`. The complex-point Nullstellensatz plus prime-ideal radicality then puts the equation in the original ideal. Irreducibility includes an explicit nonempty point. For a hypothetical proper two-closed-set cover, the proof obtains homogeneous separating equations, puts their product in the prime ideal, and derives a contradiction from one factor. Finally, full affine-cone span yields full projective span through the proved representative bridge. These are substantive consequences of the frozen algebraic conditions, not assumptions hidden in an admissibility field.

**Coordinate invariance.** Transport retains the same ideal and changes coordinates by the genuine inverse linear equivalence. Cone, rank decompositions and coordinate images of rank loci agree in both directions. The proof establishes equality of every rank-length predicate and every border-length predicate before taking their infima. It therefore preserves the mathematical objects rather than exploiting a coincident default value of an infimum. The map on projective points is the actual `Projectivization.map` induced by the linear equivalence.

## Verification and limits

I independently rebuilt Definitions and all five modules in order in `/private/tmp/nla-tr27-semantic-chain-referee-2-build`, using pinned Lean 4.33.1 and the installed campaign package cache. Every compile exited 0. A separate retained audit imports that fresh chain and prints the transitive axioms of all 41 public declarations: each has exactly `propext`, `Classical.choice`, `Quot.sound`. Source inspection found no `sorry`, `admit`, added axiom, native decision call, unsafe declaration or Challenge import in these modules. Final input hashes were compared with the hashes captured before the build and were unchanged.

This is an independent module-level source and local development-build review. It does not attest a clean Linux kernel replay, authenticated dependency retrieval, an executed full Lean4 Comparator run, a completed LeanCert verification command, the remaining concrete rank/counterexample proofs, or a complete-problem final review. Those package-level gates remain required. The whitespace-normalized statement check is explicitly supplementary and is not presented as Comparator.

## SHA-256 bindings

- `NLA/TR27/Definitions.lean`: `5f9cbf71a854a8a8a968ea4713c12bf501726e294ed7cccacff390dafb687056`
- `Challenge.lean`: `158b0f5d8eb23a3165caecf7ceed5c3f6ab87310c0576bbe9f57cbe3cfbe0ee5`
- `NUMERICAL_TARGETS.md`: `409ce7140efd7b6bab005968d5af6ef28df6f795d79276919acf408d62edca52`
- `development_proofs.py`: `029323db4d824539955522b2c9d47b9a0603fc929b7c6775189a1fb108482f13`
- `NLA/TR27/Semantics.lean`: `d1a2e30e0cec093d276c529268d8744e5c53b04706499b58827c435cf460142c`
- `NLA/TR27/SegreSemantics.lean`: `d6fc909c5a41ce146aa5883f6588537d2829f60937a1b781507d8743550d4489`
- `NLA/TR27/AffineBorder.lean`: `823403583e3b3194b8166bf86aa81afae36a0e6e047390afd0367ab269c322c9`
- `NLA/TR27/ProjectiveGeometry.lean`: `6003e71fe3beb48a768c62cff8199f39eefe05d29f0e6123195a763e9a9bf8bb`
- `NLA/TR27/CoordinateTransport.lean`: `9c9311048ca3dfb4ca2f596af78e224aea61bc1e254f6c4b420fef7475fe98c9`
- `reviews/statement-freeze.json`: `eb8ff766498145f9a5bbadcb7f7e0a2a8e62c2cd46bf1408647efc4f7b70a377`
- `reviews/semantic-chain-referee-2-evidence/Axioms.lean`: `329021713c8cea4c88a02745a3333aa763ea0cd6cae62244a3cd8351cd4984cb`
- `reviews/semantic-chain-referee-2-evidence/audit_axioms.py`: `87dc5bbeafdf8b475399d5df38a6bccdea30121f8a925f4ece754861fcb8cb5a`
- `reviews/semantic-chain-referee-2-evidence/typecheck.log`: `3f46edb96be288bfef4cfe6c3b352d24d8d1d530742b7d42fd8881d9c5e9875e`
- `reviews/semantic-chain-referee-2-evidence/axioms.log`: `8a3082828d62e08071df43f138311849c68fedc40e61c53193553c3a22c7ea07`
- `reviews/semantic-chain-referee-2-evidence/signature-check.json`: `fd2f677c1cad91cce89e318130f328c2cfade7b37cdf78808308d2a8f4410847`
