# RA-07 independent final proof review — referee 2

**PASS for the complete canonical affirmative assertion and all six frozen
exports.** No mathematical or Lean correction is requested. This permits the
candidate to proceed to actual Linux Comparator and kernel replay; it does not
claim those later operational checks have already run.

Reviewer: coordinating agent `/root`, independent of the proof implementation
by `/root/solved_statement_inventory`. Date: 12 September 2026. I previously
reviewed the statements, then independently read the completed implementation,
the retained canonical page and the relevant complete source proof. I did not
modify the candidate's mathematical files. This is AI-agent review using the
relevant Tau Ceti criteria, not external human peer review, formal verification
of the Lean implementation itself, or endorsement by Tau Ceti.

Mathematical source: Matthew J. Colbrook, Department of Applied Mathematics and
Theoretical Physics, University of Cambridge, *Convexity of a volume-sampling
error sequence*, Theorem 1.1. Formalization: George Stepaniants, Department of
Computing and Mathematical Sciences, California Institute of Technology,
Pasadena, California, USA, with substantial AI-agent assistance.

## Exact reviewed version

The proof freeze `verification/proof-freeze.json` has SHA-256
`ecd94daf2dee9fe4625e09f1a08026eb75ac8a14bea6efb688921a3e78eb6b4a`.
I independently rehashed all 38 bound project inputs and the three original
sources, and compared the latter byte-for-byte with upstream revision
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. They are unchanged.

| File | SHA-256 |
| --- | --- |
| `NLA/RA07/Definitions.lean` | `5eb47e2450eefe5a83e583173ac1de48c67be502a73f52cb4856a26c3fffb9ff` |
| `Challenge.lean` | `013fe0fd10b21a4e09260ea07477f8b6314e36df8cad9863274b486115de20cf` |
| `NUMERICAL_TARGETS.md` | `d608c6dd1b09a0c3425c740ca159bb317a4b5079dd4d128ad52239af6f8b4dcc` |
| `NLA/RA07/Algebra.lean` | `1be33b680d0f66d793a564ec22aae8996474aa85f7699f4d1dff6639903cf013` |
| `NLA/RA07/Roots.lean` | `ccbb931696ed1fafcda2518daaccee8eacb201a10eaedefd694f573b44adecde` |
| `NLA/RA07/Sums.lean` | `6a1410ed2efe6155f2f27c22b8afe37ffd0110812850f0d336c9ffee2dd8050b` |
| `NLA/RA07/Proof.lean` | `20c4d2a1078495b442f74126b42e0960462a1e82e3c5aec0b2c09065921dd21d` |
| `Solution.lean` | `55ea9b34825481eb10fefc6409eab16db61849663849f2ca09f6ceb8a1857114` |

Both statement approvals precede proof implementation and remain bound by the
freeze. The six public Solution signatures equal the frozen Challenge
signatures after whitespace normalization. The actual Comparator configuration
selects exactly those six names, no definition exceptions, and only the three
permitted axioms. This local signature check supplements the later Comparator;
it is not represented as an execution of the Linux checker.

## Mathematical and definition correspondence

The canonical target quantifies every n ≥ 3, every strictly positive real
tuple, and every 2 ≤ j ≤ n−1. `ConvexityConjecture` preserves these ranges and
the actual second difference. The elaborated definitions use real arithmetic,
the actual finite subset sum over `powersetCard`, the coefficient (j+1), and
ordinary real division. They do not use a substituted sequence, positivity
axiom, root table, or dimension-restricted witness.

`Algebra.lean` proves the empty, oversized and positive subset-sum cases. Its
product expansion is the actual generating polynomial: `prod_one_add` followed
by coefficient extraction recovers exactly the subsets of cardinality j.
Actual iterated derivative coefficients give j! e_j; the factorial is not
silently omitted. Since j! is nonzero over the reals, the subsequent ratio
cancellation is valid, including zero numerators.

`Roots.lean` proves the degree n of the actual product, then the exact degree
n−d of its actual derivative. I inspected the pinned characteristic-zero
`Polynomial.natDegree_derivative`, which is an equality, rather than treating
the weaker derivative-degree upper bound as an equality. The implementation's
induction is valid over the real coefficient field, including constant and
zero derivatives in the generic degree lemma.

The complex-root argument supplies the root location used by the factorization.
The original product roots lie on the strictly negative real ray. This ray is
convex in the complex plane; actual Mathlib Gauss–Lucas puts derivative roots
inside it whenever the input derivative has positive degree. The degree premise
is proved at every inductive step. Real splitting is then derived by descending
the actual complex splitting and verifying that every complex root lies in the
range of the real embedding. This is a legitimate replacement for the source's
Rolle argument, not an additional assumption about the derivatives.

The factorization uses the full root multiset, with its cardinality equal to
the actual degree, followed by an enumeration of every occurrence. Thus repeated
roots retain their multiplicities. Negated reciprocal roots are strictly
positive, and evaluation at zero gives the normalization factor Q(0). This
factor is separately proved positive. The d = n case has the empty root tuple
and constant product one, so no positive-degree assumption leaks into it.

`Sums.lean` differentiates the actual finite product three times and proves both
pair identities algebraically. Symmetry splits the double sum into the two
strict-order halves, with the diagonal treated explicitly. The nonnegative gap
is exactly the sum over a < b of μ_a μ_b (μ_a−μ_b)^2. The separate identity
s1²−s2 = 2 Σ(a<b) μ_a μ_b participates in the denominator proof, as promised by
the approved statement plan. For at least two factors, the pair of indices zero
and one is strictly positive. Distinct values are not assumed, so zero gaps and
equal spectra remain allowed.

`Proof.lean` transfers every ratio at index d+k to the factor tuple by actual
iterated differentiation and cancellation of the nonzero common scale. At an
original index j it uses exactly d = j−1 and m = n−(j−1), proves m ≥ 2, and
connects all three original sequence values. Field simplification receives the
proved nonzero denominators. The final certificate is the exact identity
2 pairGap / certificateDenominator, and its sign yields the full target.

The smallest dimension n = 3 and the final index j = n−1 are included. In the
last case the remaining polynomial has degree two and its third derivative is
zero; actual derivative formulas and the oversized subset-sum convention
handle this without a limiting argument. No lower-dimensional set or repeated
root configuration is removed.

The source's strict monotonicity, additional convexity index one, sampling
expectation identity, Jensen application and stable-rank estimates are outside
the formal exports. They are additional source results, not requirements of
the original canonical convexity assertion being promoted.

## Fresh compilation and trust inspection

I freshly elaborated Definitions, Algebra, Roots, Sums, Proof and Solution to a
separate output prefix, in dependency order. The fresh project artifacts take
precedence over existing project artifacts; pinned dependency build caches
were reused. All six commands returned zero without warnings. The 12 source
kernel trust assertions and actual axiom reports—six internal completed targets
and six public exports—passed with exactly `propext`, `Classical.choice`, and
`Quot.sound`. All ten dependency checkouts are clean at their exact manifest
pins. This is macOS arm64 validation, not Linux isolation or a full dependency
source rebuild.

My separately written inspection module traversed the actual proof bodies
from all six public exports. It visited 62 project declarations and explicitly
required 14 substantive dependencies, including actual Gauss–Lucas, real
splitting, full root factorization and cardinality, exact derivative degree,
iterated derivative coefficients, both pair identities, finite product
differentiation, and the original-to-shifted ratio bridge. All were retained in
the completed proof graph. I read the resulting dependency and elaborated
definition output. Six further public kernel trust checks also passed.

LeanCert is used in its explicit kernel auditing role, exactly as approved at
the statement stage. I inspected the pinned `#assert_trust` implementation: it
rejects sorry, custom axioms and native-compiler dependencies for this mode.
This exact algebra/root-geometry theorem does not need interval arithmetic;
there is no decorative numerical certificate, approximate root search, native
evaluation shortcut or finite test substituted for a universal argument.

The implementation sources have no proof holes, custom axioms, unsafe or native
shortcuts, metaprogrammatic environment mutation, or import of Challenge.
Source scanning supplements the fresh elaboration and actual axiom traversal;
it is not the sole trust check.

## Retained evidence and release gate

[Independent evidence](proof-referee-2-root-evidence/manifest.json) binds the
fresh driver, exact commands and raw logs, axiom records, source identity audit,
dependency pins, separately written inspection, and read-library hashes. Its
SHA-256 is `082af074e5195fc8ee872617bb49fe29012106134aa25c0dca02c4779cfd8609`.
The independent inspection log SHA-256 is
`9deb2b9a557241b06ae15097efa1b9db2bbea00dd41887018304ca7e3b7949e1`.

This review approves the full mathematical proof and local Lean trust boundary
for the exact frozen version. Actual Linux Comparator, default-kernel replay,
sandbox negative controls, operational evidence audit, truthful publication
manifest and final publication review remain separate gates. No canonical
status, ID, Git commit, push or PR was changed by this review.
