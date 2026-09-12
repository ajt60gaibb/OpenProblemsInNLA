# IE-19 Lean formalization

This project proves the negative answer to the [original IE-19 question](../README.md): an admissible order-three matrix has inverse row-sum norm `7/9`, strictly below the proposed `5/4`. It formalizes Matthew J. Colbrook's counterexample, then derives the negation of the complete universal conjecture. His additional sharp-infimum theorem is outside this project's formalized scope.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. Original counterexample and informal proof: **Matthew J. Colbrook**. See [formalization.yaml](formalization.yaml) for source attribution and automation disclosure.

The proof builds with the pinned Lean 4.33.1 toolchain. All exported theorems pass `#assert_trust kernel`, and their reported transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. Two independent final proof referees approved the proof and successfully re-elaborated it. The [successful Linux Comparator run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34703188616) verified all three declarations at [immutable proof revision 531941c](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/531941ca0062049ccf03d3f2df418ea805ac4036/linear-systems-and-elimination/IE-19/lean) on GitHub Actions Ubuntu 24.04. The catalog status is now `Lean verified` for the complete negative resolution. The [permanent operational evidence](verification/linux-2026-09-12/) records the executed controls, original artifacts, source hashes and independent audit.

## Exact targets

The [numerical statements](NUMERICAL_TARGETS.md) and [definitions](NLA/IE19/Definitions.lean) were written and independently reviewed before implementation. [Challenge.lean](Challenge.lean) declares the independently trusted target signatures; [Solution.lean](Solution.lean) proves them in a separate environment:

- `NLA.IE19.counterexample`: all original admissibility conditions, genuine inverses for both matrices, exact maximum absolute row-sum norms, and the strict gap.
- `NLA.IE19.not_lowerBoundConjecture`: negation of the universal lower bound.
- `NLA.IE19.not_sharpConjecture`: negation of the complete original statement, including its equality clause.

The universal statement keeps weak diagonal dominance and does not add an invertibility premise. Actual invertibility is proved for the witness, so totalized inversion cannot supply a false counterexample. The norm is the literal maximum absolute row sum. [Proof.lean](NLA/IE19/Proof.lean) uses exact finite algebra and a single kernel-mode LeanCert rational point certificate; no interval subdivision or floating-point search is needed.

## Reproduction

From this directory, a development build is:

```bash
lake exe cache get
lake build Solution
```

The pinned dependency revisions are in `lake-manifest.json`. The build reports every target's axioms. The deliberate Challenge placeholders are excluded from the proof and never imported by Solution.

From the repository root on the supported non-root Linux host, authoritative verification uses the shared [harness prerequisites](../../../tools/lean/HARNESS.md):

```bash
python3 -m pip install -r tools/lean/requirements.txt
python3 tools/lean/validate_manifest.py linear-systems-and-elimination/IE-19/lean
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh linear-systems-and-elimination/IE-19/lean /absolute/path/to/nla-lean-tools
```

This requires a committed, unchanged project. The harness uses fresh input copies and the real Linux sandbox, runs positive and negative controls, and checks all three declarations with [comparator.json](comparator.json). Formal statement identity does not replace the independent review that the Challenge matches the original question.

## Evidence

The [statement and proof referee reports](reviews/) identify the exact frozen bytes. [Local build and axiom logs](verification/) report the actual development checks and their limits. The [Linux evidence archive](verification/linux-2026-09-12/) retains the actual successful [run 34703188616](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34703188616), two original artifact ZIPs with matching GitHub digests, all 29 project input hashes, tool receipts and the independent operational review. It ran remotely on Ubuntu 24.04; the operational reviewer downloaded and audited its evidence locally without claiming a local Linux rerun. The harness used fresh pinned source clones and project elaboration with the official Mathlib compiled cache. The earlier local referee reports predate this run and retain their historical pending-Linux qualifications. Documentation updates do not change the mathematical bytes checked at `531941ca0062049ccf03d3f2df418ea805ac4036`.
