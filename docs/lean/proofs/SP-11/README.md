# SP-11 proof development

**Full local proof; final Linux verification pending.**
`NLA.Proofs.SP11.target` proves the unchanged frozen
`NLA.Statements.SP11.Target` in LeanCert kernel mode. The canonical Solved
status, original text, permanent ID and source
credits are unchanged. The substantive delta theorem is H. Tracy Hall's
[*The Delta Theorem*](https://arxiv.org/html/2601.01211v1); this development
formalizes its representation route with OpenAI Codex AI agents.

The exact all-graph boundary is the published, independently reviewed
`lean-statements/NLA/Statements/SP11.lean` and its frozen `Reviewed/SP11.lean`.
The two dated statement reviews in this directory recheck that boundary.
The modules under `lean-statements/NLA/Proofs/SP11/` prove:

| Module | Actual result |
| --- | --- |
| `GreedyOrdering` | A complete greedy vertex listing exists; its earlier-nonneighbor counts obey the required inequalities. The final count determines an ambient dimension at most `n − δ(G)`. |
| `AlternatingContraction` | Contraction of an actual alternating form is exactly orthogonal to every input, over any commutative ring. |
| `AlternatingPolynomial` | Concrete polynomial alternating forms are finite sums of determinant minors with named coefficient variables. |
| `UniformLSS` | The finite, well-founded vertex recursion exists and every distinct nonedge has exactly zero inner product. |
| `PolynomialLSS` | The actual polynomial recursion has one shared coefficient family per vertex. Its nonedge Gram polynomials vanish identically. |
| `PolynomialFaithfulness` | Finitely many nonzero real polynomials can be made nonzero at one actual parameter point, yielding faithfulness when the edge/diagonal polynomials are nonzero. |
| `GramBridge` | A faithful real representation of dimension at most `n − δ(G)` yields the exact symmetric matrix and nullity required by SP-11. |
| `GreedyRelabel` | An actual vertex permutation gives a naturally greedy graph; pattern, minimum degree and rank transport back to the original labels. |
| `GardenExpansion`, `GardenColors`, `GardenTree`, `LSSGarden`, `DoubleRootGarden` | The actual Gram polynomial is a finite sum of literal signed monomials over paired tree colorings, using only the original shared `Sigma(vertex, subset)` variables. |
| `MinorBasis`, `MonomialProducts`, `GramCoefficient` | Exact coordinate-minor evaluation and coefficient isolation; a unique nonzero contributing summand makes the actual Gram polynomial nonzero. |
| `HistogramRigidity`, `ColorWeights`, `DoubleHistogramWeights`, `ColorRigidity`, `DoubleOccurrenceShape` | Equal shared-variable exponents give actual class incident sums; those sums recover all colors when actual earlier-label blockers or ties are established. |
| `CanonicalColoring`, `CanonicalPair`, `CanonicalOutputs` | The actual canonical paired coloring is admissible, has nonzero sign, and has precisely the stated conduit colors. |
| `PriorListStructure`, `PriorInsertion`, `AugmentedColors`, `LSSLabelBounds`, `OccurrenceParent`, `ColorBounds`, `OrdinaryBlockers`, `ColoringExt` | Exact sorted sibling insertion, actual occurrence paths, local blockers and coloring extensionality. |
| `DiagonalUniqueness` | Every nonzero-sign coloring sharing the canonical exponent at a diagonal entry equals the actual canonical pair. |
| `TopOccurrences`, `EdgeUniqueness` | The actual augmented top-root list supplies every exceptional blocker; the shared cap tie and ordinary parent blockers establish edge uniqueness. |
| `Final` | Every required Gram polynomial is nonzero; simultaneous real specialization, the rank bound and actual greedy relabeling prove the full original Target. |

The **actual shared-variable** polynomial recursion preserves repeated vertex
variables and occurrence multiplicities. Equality of monomial exponents
determines each vertex class's incident-color total. Induction on original
vertex labels cancels the already-fixed child totals, and actual earlier
blockers give pointwise output lower bounds. Equality of the output sums
recovers every color, proving a unique nonzero coefficient. This finite
class-sum argument supplies the required noncancellation without formalizing
a global lexicographic priority order. Every conditional helper premise is
discharged in `Final.target`; Hall's theorem is not imported as an axiom.

The support lemmas use exact algebra, finite combinatorics, and LeanCert
`#assert_trust kernel`. They require no numerical interval certificate.
Independent source reviews and fresh local-build evidence are retained here
and in [campaign verification](../../campaign-2026-10-17/verification/).
The current `lean-statements` aggregate imports the complete `Final` closure
of 36 proof modules. The
[rigidity checkpoint](../../campaign-2026-10-17/verification/SP11-RIGIDITY-SUPPORT-INDEPENDENT-REVIEW.md)
records a fresh 32-module local closure audit of 263 declarations, including
176 theorem/lemma constants. The later
[full-target review](CLOSURE_REVIEW_2_2026-10-18.md) records 39 fresh commands,
289 declarations and 199 theorem/lemma checks, including the literal Target
type, kernel trust and standard axiom closure of `NLA.Proofs.SP11.target`.
The retained [Linux support receipt](LINUX_SUPPORT_CI_RECEIPT.md) covers only
the earlier seven-module published revision; it does not cover later files.
The historical shared Comparator job verifies frozen statement identities;
it is not a full SP-11 proof comparison. The self-contained canonical project
is being assembled after independent hash-bound Challenge reviews. Final
independent reviews and a successful fresh Linux Comparator/kernel run for
that exact project remain required before canonical promotion.
