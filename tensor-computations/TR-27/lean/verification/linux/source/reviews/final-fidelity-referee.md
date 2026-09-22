# TR-27 final fidelity and scope referee

Phase: final source review, before authoritative mechanical verification. Reviewer: `/root/tr27_final_fidelity`, an independent Codex AI agent. I authored none of the original mathematical proof, frozen definitions/statements, implementation modules, or packaging. This adapts the repository's Tau Ceti review protocol; it is neither external human peer review nor official Tau Ceti endorsement.

**Verdict: APPROVE the final source's fidelity and scope. Authoritative mechanical gates remain pending.** No mathematical correction is requested. This report does not assert that Solution's LeanCert commands or the Linux Comparator have run, and does not authorize a Lean-verified status merely from referee approval. A later evidence addendum must identify the actual successful run and bind its inputs to these reviewed mathematical bytes.

## Review boundary and original target

I independently read the complete canonical TR-27 statement and Colbrook manuscript, the entire frozen Definitions and Challenge, NUMERICAL_TARGETS, all thirteen final NLA/TR27 modules, Solution, Comparator configuration, build pins, README, metadata and the repository review protocol. I first inspected the campaign proof sources, then checked that every canonical implementation module is byte-identical to the source I read. The four frozen mathematical boundary/configuration files still match the preproof statement receipt. All 25 selected declarations have exactly one implementation and one kernel-trust assertion and axiom-print command in Solution.

The original target quantifies over finite-dimensional complex vector spaces, reduced irreducible nondegenerate projective varieties, and every projective point. It asks whether a strict border-rank deficiency forces a strict rank saving at exactly the ordinary Segre tensor square. The implementation refutes that full universal assertion by a concrete twelve-dimensional admissible example with rank 3, border rank at most 2 and square rank 9. Neither the variety hypotheses nor any lower rank bound is assumed by the exported final counterexample. No finite sample, special coefficient field, positivity assumption, genericity condition or merged tensor product replaces the original problem.

The original manuscript also proves smoothness, exact border rank 2 and arbitrarily prescribed finite delays. Those strengthenings are not needed for this negative answer and are explicitly excluded from the formal claims in the final README and metadata. The weaker inequality border rank at most 2 still gives the required strict deficiency below rank 3. The informal source's authorship and stronger results remain preserved.

## Definitions, quantifiers and nonvacuity

`ProjectiveVariety` carries actual finite complex coordinates and a polynomial ideal. Its `cone` is the entire ideal zero locus. `Admissible` transparently requires ordinary homogeneity, primality, reduced coordinate ring, a nonzero point and full linear span; it contains no hidden answer or rank premise. `admissible_geometry` proves closedness, the closed-set-union irreducibility criterion and full projective span. The proof invokes the complex-point Nullstellensatz for homogeneous equations and primality for the product argument, including degree-zero equations and the origin.

`ProjectiveRankAtMost` uses Mathlib's actual projective span and arbitrary finite lists. `projective_cone_rank` proves equivalence to unrestricted complex linear combinations, explicitly handling zero summands using an existing nonzero cone point. `rank_minima` proves the relevant length sets nonempty from full span and proves their infima are attained minima. Thus no empty-infimum default supplies a rank bound. `finite_coordinates` covers finite-dimensional ambient spaces; `coordinate_transport` preserves admissibility and both ranks under actual complex linear equivalences.

The projective closure ranges over all homogeneous complex polynomials and all degrees; the affine closure uses the vanishing ideal of the full rank locus. `projective_affine_border` proves their equivalence at every nonzero representative. Its homogeneous-component argument uses every complex scaling, and its reverse implication multiplies a test polynomial by a nonvanishing coordinate to treat the zero vector even at rank zero. No Euclidean or numerical approximation substitutes for the Zariski closure.

`segrePoints` allows the two points independently in the whole variety and takes their actual tensor product over Complex. `tensor_representatives` proves nonzero tensors and representative uniqueness, `segre_cone_rank` bridges all projective decompositions to separate affine factors, and `segre_rank_minimum` proves finite spanning and genuine minima. Scalar changes are absorbed explicitly; zero tensor summands are handled. No coordinate-matrix surrogate or symmetry restriction is used.

## Concrete geometry and lower bounds

`Algebra` proves the exact linear, surjective quotient with kernel the span of the displayed center. The finite chart, infinity chart, target vector and three-term identity agree with Colbrook's twelve-coordinate construction. Nonzero target and curve representatives are proved, including the potentially exceptional finite value forced by the first coordinate.

`IntegralImage` is a substantive whole-image proof. The exact monic quadratic makes the first parameter's twelfth power integral; the mixed monomial and final coordinate make the second power integral; both parameters and the entire polynomial substitution are therefore integral. Maximal-ideal lying over followed by the complex Nullstellensatz supplies a homogeneous preimage for every zero of the kernel ideal. Both charts and complex twelfth roots identify the full image with every scalar multiple of every finite or infinity curve vector, including zero. There are no unexamined extra closure points that could invalidate a rank lower bound.

`Geometry` proves basepoint freedom, kernel homogeneity, primality, reducedness and nondegeneracy. The latter uses a genuine thirteen-point Vandermonde spanning family followed by the proved surjective quotient; it does not replace the variety by those finitely many points. `Independence` uses polynomial coefficient functionals: the tangent-annihilating polynomial covers repeated parameters, finite zero, infinity and the empty list. Its degree bound tightens when infinity occurs. Adjoining the three fixed points excludes the center from every at-most-eight-point source span. Projection then preserves independence, and the full-image equality extends it to every injective projective family on the whole variety with arbitrary representatives.

`RankWitness.witness_not_rank_two` absorbs arbitrary cone scales into arbitrary coefficients, combines the proposed at-most-two-parameter set with the three fixed parameters, and separates a missing fixed point using independence of the union. The upper bound uses the exact three-term identity. Its square upper bound expands that identity in the actual tensor product and enumerates all nine pairs.

For the square lower bound, `cone_square_parameters` normalizes each factor independently, including zero factors. `square_parameter_lower_bound` collects the distinct left and right parameters separately, each with cardinality at most eight. Actual tensor contractions place the target in both spans. Any expansion of that target has at least three nonzero weights, by the rank-two exclusion. Extended dual coordinates show that every pair in the Cartesian product of the two nonzero supports must occur among the proposed summand pairs. This forces at least nine pairs into a set of at most eight. Repetitions, cancellation, zero coefficients and unrelated factors cannot evade this count.

`BorderWitness` proves an everywhere-nonzero polynomial divided-difference curve with two terms away from zero. Substituting any polynomial that vanishes on the whole rank-at-most-two cone gives a univariate polynomial vanishing away from zero; multiplying by X and polynomial extensionality make it identically zero. Evaluation at zero yields the target. The proof is exact algebra with no sampling, approximate arithmetic or missing limit bridge.

`Counterexample` combines these statements through the proved rank/minimum/closure and Segre bridges to obtain ranks 3 and 9 and border rank at most 2. It explicitly checks that the tensor point is the square of the chosen projective representative. The last theorem applies the universal conjecture to this admissible example and derives the impossible inequality 9 < 9.

## Publication scope, attribution and findings resolved

The permanent TR-27 canonical README path, original mathematical target, problem source and ID registry have no diff against the original canonical base. The final package preserves Colbrook's mathematical authorship and credits George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, for the formalization, without adding a contact email. The existing source manuscript is left intact. AI authors and independent referee roles are disclosed without human-review or official-endorsement claims.

My preliminary documentation finding was stale development wording in automation metadata and incomplete AI module-role attribution. The final metadata now records completed roles accurately; the README expressly treats unchanged draft comments in the frozen specification and earlier module headers as historical. The Lake default target is Solution and both Challenge and Solution have separate libraries. Those concerns are resolved without any mathematical boundary change.

## Mechanical evidence actually inspected

I read `reviews/complete-local-development.log` completely: the thirteen-module chain, including Counterexample, exits zero under Lean 4.33.1 on macOS; its printed final theorem axiom closures contain only `propext`, `Classical.choice` and `Quot.sound`. I also read `reviews/rank-author-evidence/development-typecheck.log`, including successful RankWitness elaboration and its helper/target axiom audit. These are development logs produced by other agents, not a Linux run performed by this referee. I did not infer mathematical fidelity from their PASS labels; the source scrutiny above is independent.

I independently ran source-hash, implementation-coverage, trust-command-coverage and forbidden-source/import checks. No implementation placeholder, custom axiom declaration, native-decision shortcut, implementation override or Challenge import was found in the final proof chain. Comparator selects all 25 required statements with no definition holes and permits exactly the three standard axioms. Solution sets LeanCert trust to kernel and asserts that level separately for each selected theorem.

At this receipt, Solution's actual LeanCert elaboration, the real non-root Linux sandbox/rejection controls, all 25 Comparator comparisons, fresh kernel replay and the authoritative transitive axiom gate are still pending. Source approval cannot replace any of them. The other independent final referee is a separate gate. This report makes no claim about a run not yet inspected.

## Exact reviewed bytes

The publication checkout base is `daf313133bfe730c32a266ea85cd9ca0fbe2d5ed`; the original target base is `54f93060c0c4e5dab81096c6496e0d2b4251f3ef`. Source identity is bound by SHA256 below, not by an uncommitted branch label. Paths in the first table are relative to the canonical `tensor-computations/TR-27/lean` directory. A machine-readable record with checks and pending gates is `final-fidelity-source-receipt.json` beside this report.

| File | SHA256 |
| --- | --- |
| `NLA/TR27/AffineBorder.lean` | `823403583e3b3194b8166bf86aa81afae36a0e6e047390afd0367ab269c322c9` |
| `NLA/TR27/Algebra.lean` | `ce5694407e1e40b201746dc52897ea05acbb69c27efa6c79bfb700fe070d5134` |
| `NLA/TR27/BorderWitness.lean` | `2f19534138b25ca09056ef1a106565d7ad2d39394bca6b6fa75f33901f49b068` |
| `NLA/TR27/CoordinateTransport.lean` | `9c9311048ca3dfb4ca2f596af78e224aea61bc1e254f6c4b420fef7475fe98c9` |
| `NLA/TR27/Counterexample.lean` | `3a60daa4269e946d7aa1e02813e7f5178a6c35125072789581a7d37c23424bef` |
| `NLA/TR27/Definitions.lean` | `5f9cbf71a854a8a8a968ea4713c12bf501726e294ed7cccacff390dafb687056` |
| `NLA/TR27/Geometry.lean` | `4f067416b429e37e0b34a24d764cc75d895ca7b6bcbfb20c42edd8f5c2809472` |
| `NLA/TR27/Independence.lean` | `e7394b4445160b14a7754d3d234d43abb1e90d43eed288c32e38c892ad179b0e` |
| `NLA/TR27/IntegralImage.lean` | `72e1d5af05acc5e7497d1db2f81d6c3585497a76bdcc4577eea6c2efa783bd89` |
| `NLA/TR27/ProjectiveGeometry.lean` | `6003e71fe3beb48a768c62cff8199f39eefe05d29f0e6123195a763e9a9bf8bb` |
| `NLA/TR27/RankWitness.lean` | `bd7d4644ca96c951aaac781ed8c448d21bb20a49c26638079163c0c08e3db4da` |
| `NLA/TR27/SegreSemantics.lean` | `d6fc909c5a41ce146aa5883f6588537d2829f60937a1b781507d8743550d4489` |
| `NLA/TR27/Semantics.lean` | `d1a2e30e0cec093d276c529268d8744e5c53b04706499b58827c435cf460142c` |
| `Solution.lean` | `5b4acf9113d48d69e3a4834a45dd886c59ffbe48355934d766e71fa3230d9a10` |
| `Challenge.lean` | `158b0f5d8eb23a3165caecf7ceed5c3f6ab87310c0576bbe9f57cbe3cfbe0ee5` |
| `NUMERICAL_TARGETS.md` | `409ce7140efd7b6bab005968d5af6ef28df6f795d79276919acf408d62edca52` |
| `comparator.json` | `2cf6d47dd9b3ad53fabd80b87c49476eefebd07c930994929a8534a0d8b46291` |
| `lakefile.toml` | `8bbc3712ddc448128c51d29cd0391b14d5ccc030584e7188274cea40b960f7f2` |
| `lake-manifest.json` | `dc5d5e3067aaa5b8e5fa140ba328adaf525a8c31a4968108db28724475a78df6` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `README.md` | `b7046d561896781f27b7d9a0af549c64239c9dd0d9fdd033efd41d21bd65844b` |
| `formalization.yaml` | `7b6af62fd77576e311ed427125c163e3c99eff80e1ef21db89b162a0082783b9` |
| `reviews/statement-freeze.json` | `eb8ff766498145f9a5bbadcb7f7e0a2a8e62c2cd46bf1408647efc4f7b70a377` |
| `reviews/complete-local-development.log` | `1c944c93987e9b9e57c4be1857608c56ed05df6c1f5465f4716dc10c8c6e77fb` |
| `reviews/rank-author-evidence/development-typecheck.log` | `3c5a4616f7a65b9bdbe5a01421060fa3b2872825c3d708faa97e8b0a87a698a2` |

Original inputs, relative to the repository root:

| File | SHA256 |
| --- | --- |
| `tensor-computations/TR-27/README.md` | `111ccd36436f926608d1e604ed974d82dfe9ece400c7ac2ce8710d96d00b2e00` |
| `tensor-computations/TR-27/problem.tex` | `1d49bcfaaf55ba4b2f8e6bd4bbb23dd3376b2c6da1366a411f7d97c564b95359` |
| `references/colbrook-tensor-metrics-rank-2026-09-11/manuscripts/tr27_solution.tex` | `e554971c970e05efb61675f35d66bdc4847266fe5eba86e8cb445043fb83be67` |
| `docs/lean/REVIEW.md` | `d967ddce620d4e754e2f9c25548f30cb537f76f4ddcf8ecf2574945bcd332553` |
| `problem_ids.json` | `d7f9925a483d40030ef266917bc8e413dac6d45530ad5515da506ffe9583e763` |
