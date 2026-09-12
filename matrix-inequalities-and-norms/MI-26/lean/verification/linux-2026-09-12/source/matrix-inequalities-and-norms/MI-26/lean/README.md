# MI-26: formal counterexample to concave unitary-orbit subadditivity

The complete canonical MI-26 assertion has a local Lean proof with two independent
statement approvals and two independent final proof approvals. **Authoritative
Linux Comparator, default-kernel replay and isolation/rejection controls remain
pending.** The canonical problem status remains **Solved**.

**Mathematical counterexample and informal proof:** Matthew J. Colbrook,
Department of Applied Mathematics and Theoretical Physics, University of Cambridge.
**Lean formalization:** George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA, with
substantial AI-agent assistance. No external human peer review or source-author
endorsement is claimed.

The [original problem](../README.md) and [complete source proof](../solution.tex),
Theorem 1.1 and its proof, were reviewed at
`587bd896f0e1006f4a4b7f38555e3a523ef85176`; they remain unchanged at integrated
upstream base `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.

## Complete scope and calculation

The conjecture quantifies over every positive dimension, every pair of complex
positive-semidefinite matrices, every real-valued concave function on the
nonnegative half-line with `f(0) ≥ 0`, and existence of two complex unitaries. The
formalization proves its **full negation** using `f(x)=x-x²`,
`P=diag(1,0)`, `Q=[[9,12],[12,16]]/25` and `w=(1,-2)`.

Both actual matrix-function values `f(P)` and `f(Q)` vanish. Genuine continuous
functional calculus gives
`f(P+Q)=[[-18,-12],[-12,0]]/25`, whose quadratic form at `w` is exactly `6/5>0`.
Therefore it cannot be dominated by the zero sum of the two unitary conjugates.
Exact algebra handles the entire matrix calculation; the only numerical
certificate is explicit kernel-mode LeanCert for `0<6/5` on a singleton interval.
That certificate is retained in the all-unitary contradiction.

The function class is real-valued: global nonnegativity and monotonicity are
absent. This formalization makes no claim against the narrower globally
nonnegative-valued function class. The informal source's additional
positive-definite variant is outside the exported claims; the original PSD target
is completely negated.

Seven exports in [Solution.lean](Solution.lean) are registered in
[comparator.json](comparator.json):

| Export in `NLA.MI26` | Formal scope |
|---|---|
| `admissibleFunction_iff` | Exact equivalence to the original scalar concavity formula and `f(0)≥0`. |
| `functionalCalculus_eq_spectral` | Actual CFC equals the complete spectral formula for any real function on a complex Hermitian matrix, with no continuity premise. |
| `functionalCalculus_congr_nonneg` | Extensions outside the original half-line do not change CFC at PSD inputs. |
| `quadratic_cfc` | Genuine CFC for the witness polynomial equals `A-A²` on every Hermitian input. |
| `witness_data` | All function and matrix admissibility conditions, projection identities, CFC values and exact positive quadratic form. |
| `counterexample` | Exclusion of every pair of genuine complex unitaries. |
| `not_subadditivityConjecture` | Unconditional negation of the complete canonical target. |

The definitions and numerical obligations were frozen before implementation in
[Definitions.lean](NLA/MI26/Definitions.lean), [Challenge.lean](Challenge.lean), and
[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md). A whole-real-line extension represents
the original half-line function; its values outside that half-line are proved
irrelevant. The generic spectral bridge handles even functions discontinuous at
zero because the matrix spectrum is finite. No default CFC fallback, sampled
unitary, real-only matrix restriction, or entrywise polynomial surrogate replaces
the problem's mathematical objects.

## Reproduction and current checks

```sh
lake build Solution
```

The pinned project uses Lean `v4.33.1`, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`; the complete ten-package manifest is
[lake-manifest.json](lake-manifest.json). `Proof.lean` and `Solution.lean` explicitly
select `leancert.trust "kernel"`. All **15** internal/exported trust and axiom
checks passed with exactly `propext`, `Classical.choice`, and `Quot.sound`.
The local build reported **3147 jobs** without warnings. Matching dependency
artifacts were reused on macOS arm64; this is not a full dependency rebuild or an
authoritative Linux run.

After committing this candidate, run from the repository root on supported Linux:

```sh
tools/lean/bootstrap.sh /tmp/nla-mi26-tools
tools/lean/selftest.sh /tmp/nla-mi26-tools
tools/lean/verify.sh matrix-inequalities-and-norms/MI-26/lean /tmp/nla-mi26-tools
```

The shared GitHub workflow performs these checks with pinned tools, a fresh
tracked-source snapshot, the real sandbox, all seven statement comparisons and
rejection controls. Its actual MI-26 results will be recorded before promotion.
Comparator checks the formal Challenge/Solution boundary and kernel proof;
independent referees separately review correspondence to the informal problem.

- [Statement referee 1](reviews/statement-referee-1.md) and [statement referee 2](reviews/statement-referee-2.md) approved the unchanged boundary before proof work.
- [Final proof referee 1](reviews/proof-referee-1.md) and [final proof referee 2](reviews/proof-referee-2.md) independently inspected and freshly re-elaborated the actual source and certificate consumers.
- [Proof completion](reviews/proof-completion.md), [frozen identities](verification/proof-freeze.json), [local build](verification/proof-build.log), and [axiom audit](verification/proof-axioms.json) retain the evidence.
- [formalization.yaml](formalization.yaml) follows the pinned schema-v0.4 standard and records authorship, exact scope, automation, theorem coverage and pending Linux status.

The implementer `/root/leancert_examples` is not counted as its own referee.
The independent reviewers are `/root/solved_statement_inventory` and `/root`,
using the project's adapted Tau Ceti rubrics. Seven deliberate Challenge
placeholders are isolated from every proof import and excluded from solution
sorry counts. Historical statement/proof-freeze notes retain the status at their
creation; the final referee reports and this guide supply the current local-review
status. No proof or statement bytes were changed while preparing this package.

Shared checker reuse from [Forsythe](https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof)
is credited in [tools/lean/NOTICE.md](../../../tools/lean/NOTICE.md). The campaign also
consulted [Schiffer](https://github.com/jaumededios/Schiffer/tree/2938e277969c329caf154e48a3d8823f3635c7f1)
for project organization; neither example supplies an assumed mathematical result
of MI-26.
