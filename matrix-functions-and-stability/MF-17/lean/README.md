# MF-17 Lean formalization

The mathematical target and its proposed manuscript proof appear in Part VI of
[MF-17-research-handoff.pdf](../MF-17-research-handoff.pdf). The formalization
uses adapted symbolic arguments, including a scalar lower construction and
refined constants; [the correspondence notes](NUMERICAL_TARGETS.md#adaptations-of-the-manuscript-proof)
identify these differences explicitly.

With Lean installed through [elan](https://github.com/leanprover/elan), run
from this directory:

```sh
lake exe cache get
lake build Solution
```

`lean-toolchain` selects Lean 4.33.1. Mathlib and its dependencies are pinned
in `lake-manifest.json`.

[Solution.lean](Solution.lean) imports the complete formalization. The main
theorems, in namespace `ProofProject`, are:

| Theorem | Result |
| --- | --- |
| `stableSemigroup_hasGeneratorInverse` | The full generator has a unique bounded, everywhere-defined inverse. |
| `attainableNorms_bddAbove` | The growth envelope is finite at every nonnegative time. |
| `contractive_envelope` | The envelope is exactly one when M = 1. |
| `finite_dimensional_lower` | Finite-dimensional witnesses attain the lower bound with the exact semigroup bound M. |
| `sharp_growth` | For each M > 1, the envelope has matching upper and lower bounds of order (log log(t + exp(exp(1))))^((2/π) arccos(1/M)). |

[Definitions.lean](ProofProject/Definitions.lean) defines strongly continuous
semigroups, the full generator graph, its inverse, and the growth envelope.
The formalization allows unbounded generators and arbitrary complete complex
Hilbert spaces in a fixed universe. The constants in the asymptotic bounds
depend only on M.

## Verification

`Challenge.lean` states the five contracts in an independent environment.
Its five deliberate specification placeholders are excluded from the proof
side; `Solution.lean` does not import it. `comparator.json` selects all five
contracts and permits only the standard foundational axioms.

For local development checks, run:

```sh
LEAN_NUM_THREADS=2 lake build Challenge Solution
lake env lean verification/StatementTypes.lean
lake env lean verification/Axioms.lean
```

The target-to-source correspondence is in [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md).
Independent retrospective source reviews are retained in [reviews](reviews/).
The [verification report](verification/README.md) records the successful local
build, five target-type and axiom checks, and complete fresh Linux Comparator
and default-kernel run on 30 September 2026. The checked source revision is
`ac582d01532a914538cbfb74863437b18433038a`; subsequent changes add evidence
and publication metadata without changing the Lean sources or contracts.
The manifest distinguishes retrospective AI source review from actual runtime
verification. The [published source snapshot](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/cad3785440a2678b5b30aa8133d425e709b6811d/matrix-functions-and-stability/MF-17/lean)
contains the same Lean sources, contracts and dependency pins, as checked
against the receipt hashes in the [maintainer integration review](reviews/maintainer-integration-2026-09-30.md).
The run's original local commit was not published; use the published snapshot
to reproduce its mathematical inputs.

For the repository's authoritative check, use the shared
[Linux verification workflow](../../../tools/lean/HARNESS.md) from the repository
root, on a non-root Linux runner with the required systemd user session and
sandbox support. See `../../../tools/lean/HARNESS.md` for prerequisites.

From the repository root, reproduce the authoritative run with:

```sh
python3 tools/lean/harness.py bootstrap /tmp/mf17-tools
python3 tools/lean/harness.py verify \
  matrix-functions-and-stability/MF-17/lean /tmp/mf17-tools
```
