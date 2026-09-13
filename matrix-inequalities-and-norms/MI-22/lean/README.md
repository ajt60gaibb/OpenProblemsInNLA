# MI-22 — complete Lean counterexample with verified Linux evidence

**All eight target exports are proved and have two independent statement approvals and two independent final proof approvals.** Actual [Linux run 34720684925](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34720684925) passed the sandboxed Comparator, Lean default-kernel replay and both exercised control suites at immutable proof revision [`26f526cf`](https://github.com/sgstepaniants/OpenProblemsInNLA/commit/26f526cf8b6232af9528b30616076dc7a2c66ac6). The [separate independent operational audit](verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) passed. The publication package records the canonical status as **Lean verified**, subject to the final repository publication review.

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

## Independent reviews and actual Linux verification

- Statement referee 1: [report](reviews/statement-referee-1.md).
- Statement referee 2: [report](reviews/statement-referee-2.md).
- Final proof referee 1: [report](reviews/proof-referee-1.md), [independent raw evidence](reviews/proof-referee-1-evidence/EVIDENCE-MANIFEST.json).
- Final proof referee 2: [report](reviews/proof-referee-2.md), [independent raw evidence](reviews/proof-referee-2-root-evidence/manifest.json).

These are independent AI-agent reviews applying the [NLA adaptation of Tau Ceti standards](../../../docs/lean/REVIEW.md), not human peer review or source-author endorsement. The separate operational reviewer `/root/formal_review_standards` did not implement this project or act as one of its two mathematical referees. This catalog reviewed the actual remote Linux execution; local macOS checks remain separately labeled.

The [archived statement-stage README](verification/candidate-2026-09-12/README.statement.md) preserves the original frozen bytes. Candidate packaging changes only this current README among the 104 proof-freeze inputs; all mathematical source, Challenge, numerical targets, source mapping, configuration, pins and review evidence remain unchanged. The candidate integrity record and handoff are retained in [verification/candidate-2026-09-12](verification/candidate-2026-09-12/).


The actual Linux receipt matched all **177 committed project inputs**, freshly elaborated the Challenge and Solution, and accepted all eight statements with no definition exceptions. Both environments were exported and the actual Lean default kernel replayed the solution. All 17 internal/public axiom reports use exactly the standard three axioms. Both the standalone checker and the MI-22 job ran the real sandbox, raw-kernel, Comparator, admitted-proof and native-proof rejection controls; details and their precise limits are in the audit.

All ten dependency repositories were freshly cloned at their manifest revisions. The official Mathlib cache decompressed 8,690 files, so this is not a complete Mathlib source rebuild. The graph sizes of 2,723 Challenge jobs and 3,163 Solution jobs are not counts of freshly compiled dependency sources. The eight isolated Challenge placeholders do not enter Solution.

The [original project/control artifact ZIPs and raw run logs](verification/linux-2026-09-12/) remain byte-identical. The [outer manifest](verification/linux-2026-09-12/EVIDENCE-MANIFEST.json) binds 303 files, and the retained directory contains 304 including that manifest; nested manifests are included. The original artifact digests match GitHub metadata and upload logs. Offline verification is available without another Linux run:

```
python3 verification/linux-2026-09-12/verify_evidence.py
```

To reproduce the authoritative checks from the repository root on a non-root Linux host meeting the [harness requirements](../../../tools/lean/HARNESS.md):

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-22/lean \
  /absolute/path/to/nla-lean-tools
```

The [publication record](verification/publication-2026-09-12/) archives the exact pre-execution candidate README and metadata and binds their permitted documentation updates. Only the current README and formalization.yaml change among the 177 verified inputs; the other 175, all mathematical source and all 304 Linux-evidence files remain unchanged. The exact original source target and original informal resolution are preserved. No repeated Linux run or new mathematical proof is claimed for these documentation changes.

The current canonical README and its generated TeX/PDF are updated only to add the verification notice and current status. Their original checked versions remain in the immutable Linux source archive; the five original informal-proof and source-review inputs remain byte-identical. The entire original problem statement and later source/reference text are unchanged.
