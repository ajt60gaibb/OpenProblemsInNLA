# MI-22 — complete Lean counterexample, Linux verification pending

**All eight target exports are proved and have two independent statement approvals and two independent final proof approvals.** Local checks passed using only the standard three axioms. The actual Linux sandboxed Comparator/default-kernel run and its independent operational audit are still pending. The canonical problem remains **Solved**.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. AI-assisted implementation by agent `/root/leancert_examples`; that implementer is not counted as an independent referee. Matthew J. Colbrook retains attribution for the original negative resolution and mathematical method.

## Full original scope and adapted witness

The [canonical target](../README.md) quantifies every positive dimension, every complex positive-definite pair A,B and every real t in [0,1]. The actual weighted product is `A^t (A #_t B) B^(1-t)`. Its claimed singular-value log-majorization includes every proper prefix inequality **and equality of the full products**. The final export negates that entire original statement.

The formalization preserves the source's diagonal A, but uses the disclosed exact rational adaptation **B=D T⁸ D**, not Colbrook's printed integer B. The exact T, its source provenance and every required certificate are fixed in [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) and [SOURCE_CORRESPONDENCE.md](SOURCE_CORRESPONDENCE.md). Their statement-stage descriptions are historical records preserved byte for byte. This project does not advertise a verification of the original printed B, its residual-to-root lemma or the source's 10900/10200 thresholds.

All powers are genuine Mathlib CFC powers, and all singular values are the actual descending Euclidean-map singular values, retaining multiplicities. The generic exported theorems prove their spectral semantics and the genuine operator/Frobenius/action bounds. Exact LDL and matrix algebra prove positivity and all numerical certificates as conclusions. For the actual root Y=B^(1/8), the proof establishes Y⁸=B and the noncommuting identity L Y=N. The positive trace bound gives ‖Y‖₂<4; an exact unit-vector coordinate exceeds 44000, forcing ‖L‖₂>11000. The exact Frobenius estimate gives ‖AB‖₂<10500. Thus the actual first singular values reverse the required k=1 inequality at n=3,t=1/8, refuting the full universal statement.

## Files and exported results

- [Definitions](NLA/MI22/Definitions.lean) and the independently approved [Challenge](Challenge.lean) state the unchanged mathematical boundary.
- [FunctionalCalculus](NLA/MI22/FunctionalCalculus.lean), [Norms](NLA/MI22/Norms.lean) and [SingularValues](NLA/MI22/SingularValues.lean) establish genuine generic semantics.
- [Witness](NLA/MI22/Witness.lean), [ExactData](NLA/MI22/ExactData.lean) and [Proof](NLA/MI22/Proof.lean) prove every finite certificate, true root identity and contradiction.
- [Solution](Solution.lean) exports `singular_values_semantics`, `spectral_power_semantics`, `euclidean_norm_bounds`, `witness_rational_data`, `witness_principal_powers`, `witness_operator_gap`, `counterexample` and `not_weightedLogMajorizationConjecture`, all in namespace `NLA.MI22`.
- [formalization.yaml](formalization.yaml) follows the actual pinned v0.4 metadata schema. [comparator.json](comparator.json) selects exactly those eight exports, allows only the standard three axioms and has no definition exceptions.

## Reproduction and precise trust scope

From this project directory, build the **complete proof** explicitly:

```
lake build Solution
```

The frozen default target remains Challenge, so plain `lake build` checks the statement target. The only authorized configuration change appended the Solution library; the [original lakefile](verification/lakefile.statement.toml) and [exact authorization/diff](verification/build-registration.json) remain intact.

Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` are pinned. The complete solution closure has zero admissions and exactly `propext`, `Classical.choice` and `Quot.sound` as transitive axioms. Challenge's eight intentional placeholders are isolated and never imported by Solution.

LeanCert proves the retained scalar comparison **10500<11000** in explicit kernel mode, on the singleton [0,0]. Its exact Boolean certificate is kernel-proved and consumed in the strict singular-value reversal and full negation. It certifies only this scalar separation. Matrix tables, positivity, CFC roots and norm bridges are proved with exact Lean mathematics. Three squarings and one tested row avoid matrix-root approximation, interval subdivisions and numerical singular-value computation.

The [author's completion record](reviews/proof-completion.md) and [proof freeze](verification/proof-freeze.json) bind 104 original project inputs and eight original source files. Both final referees freshly rebuilt actual proof modules in separate prefixes excluding prior project objects; they reused clean pinned dependency caches and did not claim full dependency-source rebuilds. They inspected actual declaration dependencies, all 17 internal/public standard-three reports and the retained LeanCert certificate.

## Independent reviews and remaining checks

- Statement referee 1: [report](reviews/statement-referee-1.md).
- Statement referee 2: [report](reviews/statement-referee-2.md).
- Final proof referee 1: [report](reviews/proof-referee-1.md), [independent raw evidence](reviews/proof-referee-1-evidence/EVIDENCE-MANIFEST.json).
- Final proof referee 2: [report](reviews/proof-referee-2.md), [independent raw evidence](reviews/proof-referee-2-root-evidence/manifest.json).

These are independent AI-agent reviews applying the [NLA adaptation of Tau Ceti standards](../../../docs/lean/REVIEW.md), not human peer review or source-author endorsement. Local macOS checks and exact signature comparison do not replace the [required Linux verification pipeline](../../../docs/lean/README.md). No Linux result or immutable submitted proof revision is claimed yet.

The [archived statement-stage README](verification/candidate-2026-09-12/README.statement.md) preserves the original frozen bytes. Candidate packaging changes only this current README among the 104 proof-freeze inputs; all mathematical source, Challenge, numerical targets, source mapping, configuration, pins and review evidence remain unchanged. The candidate integrity record and handoff are retained in [verification/candidate-2026-09-12](verification/candidate-2026-09-12/).
