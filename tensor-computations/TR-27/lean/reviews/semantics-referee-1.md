# TR-27 semantic proof review 1

Date: 2026-09-22. Reviewer: `/root/infrastructure_audit`, independent Codex AI
agent. I authored none of the TR-27 definitions, Challenge or proof modules.
The reviewed `Semantics.lean` was authored by `/root` after the two independent
statement reviews and statement freeze. This is documented AI review, not
external human peer review.

**Verdict: APPROVE the five auxiliary semantic proofs at the hashes below.**
No mathematical or signature change is requested. This approval covers
`finite_coordinates`, `tensor_representatives`, `cone_projective_membership`,
`projective_cone_rank` and `rank_minima`, together with their local helpers.
It does not establish the other twenty Challenge obligations or the original
counterexample. No complete TR-27 verification or status promotion is warranted.

## Exact boundary and inputs

I read the entire Definitions and Semantics modules, all Challenge signatures,
the frozen statement receipt, the semantic portions of the numerical target,
the canonical original problem, the source manuscript's rank conventions,
the prior independent statement review, and the author's development evidence.
The actual Mathlib representative, finite-span, dual-functional and infimum
lemmas used here were inspected in the retained Mathlib source tree.
That source inspection is an API check, not an independent authentication of
the extracted source directory's revision.

All five theorem signatures, including quantifiers and hypotheses, are exactly
the frozen Challenge signatures after whitespace normalization. Their ambient
namespace, complex-module variables and scope agree. Definitions and Challenge
still have the statement-freeze hashes. The proof module imports Definitions
and `Mathlib.LinearAlgebra.Dual.Lemmas`; it imports no Challenge or other
placeholder-bearing campaign module. There are no added result assumptions,
custom axioms, `sorry`, `admit`, `native_decide` or implementation overrides.

SHA256, paths relative to the TR-27 draft directory:

| Input | SHA256 |
| --- | --- |
| `NLA/TR27/Semantics.lean` | `d1a2e30e0cec093d276c529268d8744e5c53b04706499b58827c435cf460142c` |
| `NLA/TR27/Definitions.lean` | `5f9cbf71a854a8a8a968ea4713c12bf501726e294ed7cccacff390dafb687056` |
| `Challenge.lean` | `158b0f5d8eb23a3165caecf7ceed5c3f6ab87310c0576bbe9f57cbe3cfbe0ee5` |
| `NUMERICAL_TARGETS.md` | `409ce7140efd7b6bab005968d5af6ef28df6f795d79276919acf408d62edca52` |
| `development_proofs.py` | `b105fee18a726fd2e8bea0cd095521eff2f10e63e8edcce1f40a6af8044fe405` |
| `reviews/statement-freeze.json` | `eb8ff766498145f9a5bbadcb7f7e0a2a8e62c2cd46bf1408647efc4f7b70a377` |
| `reviews/semantics-author-evidence/evidence.json` | `843651904a1c4613e176c58e8e34a1fa8b5ee0a49e909ae66be7236d56487971` |
| `reviews/semantics-author-evidence/typecheck.log` | `6a2c667c4dd0b2eb573683b2c996dfbba2a3865eae62738169410c044bd3d89f` |

The canonical README retains SHA256
`111ccd36436f926608d1e604ed974d82dfe9ece400c7ac2ce8710d96d00b2e00`;
the complete Colbrook manuscript retains
`e554971c970e05efb61675f35d66bdc4847266fe5eba86e8cb445043fb83be67`.
The published base is `54f93060c0c4e5dab81096c6496e0d2b4251f3ef`.
This review changes no canonical page, permanent ID or original proof source.

## Mathematical inspection

`finite_coordinates` uses a basis indexed by the actual complex finrank and
its linear equivalence with coordinate functions. It covers every
finite-dimensional complex module, including dimension zero. It introduces
no bound on dimension. The other results obtain finite coordinates from
`ProjectiveVariety` when needed; they do not assert existence of a projective
point in the zero vector space.

`tensor_representatives` first proves that the tensor of two nonzero vectors
is nonzero. Dual functionals taking each vector to one carry that tensor to
one, so its alleged vanishing is impossible. This uses the ordinary tensor
product over Complex and independent factors. The projective point is the
actual Mathlib quotient constructor. Existence of a nonzero representative
scale follows from its unit-scalar lemma; uniqueness follows from the
projective equality criterion. `Represents` itself cannot hold for the zero
vector, as the separate helper proves from `rep_nonzero`.

`cone_projective_membership` establishes representative independence rather
than assuming it. For every homogeneous polynomial, evaluation at a scalar
multiple is the scalar raised to its degree times its original evaluation.
Each homogeneous component of a member of the homogeneous ideal remains
in that ideal. Summing the components proves closure of the entire zero
locus under scalar multiplication. This argument is valid at scalar zero
and degree zero as well. The reverse implication for a nonzero scalar uses
its inverse. Applying that equivalence to the nonzero scalar relating a
chosen projective representative and the supplied vector proves both
directions of the exact membership target. Primality and reducedness are
unneeded for this helper, but retaining the reviewed admissibility hypothesis
does not alter its required conclusion.

`projective_cone_rank` connects actual projective span to the linear span of
chosen representatives and then to finite sums with unrestricted complex
coefficients. The forward direction keeps the same length and coefficients.
In the reverse direction a zero cone vector is assigned an arbitrary fixed
nonzero cone point, supplied by admissibility. Crucially, the proof does not
incorrectly reuse that zero summand's coefficient on the replacement point:
it proves the original zero vector belongs to the resulting linear span,
then retains the original equality of vector sums. Nonzero vectors give
their own projective points. Thus the same length bound holds with zero
vectors, zero coefficients, repetitions, cancellation and arbitrary complex
scalars. At length zero, the vector sum is zero; a nonzero target cannot
satisfy either side. No distinctness or positivity condition is introduced.

`rank_minima` proves nonemptiness before using either natural-number infimum.
Full cone span gives a finite linear combination; the finite support is
reindexed by `Fin k` with its equality transported by a bijection. The
projective-cone bridge then gives an ordinary spanning length for every
actual projective point. Inclusion of a set in its all-homogeneous-polynomial
closure supplies a border length. Both predicates are monotone in the bound.
For a nonempty set of natural numbers, `csInf_mem` places the infimum in the
set; monotonicity and `csInf_le'` prove the two required equivalences. In
particular, substituting each rank for the bound proves attainment of both
minima. An empty-set default cannot enter either rank conclusion.

The closure helpers quantify over every degree and every homogeneous
polynomial in the reviewed definition. They do not substitute Euclidean
closure or a bounded polynomial family. The degree-zero constant polynomial
one excludes every point from the closure of the empty set, consistent with
the zero-length projective rank locus. The separate affine/projective border
bridge and all geometry of the concrete witness remain further obligations;
none is silently claimed by this module.

## Independent development check and limits

I reran the following command from the isolated campaign worktree, using a
new build directory containing no prior project outputs:

```bash
python3 docs/lean/campaign/2026-09-22/TR-27/development_proofs.py \
  --lean /private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean \
  --packages /private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages \
  --build-dir /private/tmp/nla-tr27-semantics-referee-1-fresh \
  --log docs/lean/campaign/2026-09-22/TR-27/reviews/semantics-referee-1-evidence/typecheck.log \
  --module Semantics
```

Both Definitions and Semantics elaborated with exit zero and no warnings.
Lean reports version 4.33.1, compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The five selected declarations
and `projective_span_range` each print precisely the transitive axiom set
`[propext, Classical.choice, Quot.sound]`. The input receipt and reproducible
textual signature audit are retained in `semantics-referee-1-evidence/`.

This check uses cached macOS dependency objects. It is not the fresh Linux
sandboxed replay, authenticated export or Comparator run required for final
publication. It also does not compile the pinned LeanCert trust assertion.
Those remain mandatory separate gates, and the textual signature audit does
not replace Comparator. There is no numerical approximation or interval
computation in these semantic proofs. The module correctly preserves George
Stepaniants's requested name and Caltech department affiliation, omits contact
email, credits Matthew J. Colbrook's original proof, and discloses AI assistance
and its incomplete auxiliary scope.
