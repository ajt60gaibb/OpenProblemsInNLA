# Lean workspace

This folder contains the Lean formalization paired with the mathematical source
and computer-assisted work in [`../proof/`](../proof/). The root Goal determines
whether Lean is the main focus, a joint track, or currently inactive.

Read [`../AGENTS.md`](../AGENTS.md) and [`AGENTS.md`](AGENTS.md) before material
Lean work.

## Core files

| File or folder | Role |
|---|---|
| `ProofProject/Definitions.lean` | Definitions needed in target statements. |
| `Challenge.lean` | Trusted target signatures with deliberate placeholder proofs. |
| `Solution.lean` | Independent proofs of the same configured declarations. |
| `ProofProject/Helpers.lean` | Proof-only lemmas, library interfaces, and checked certificate logic. |
| `ProofProject/Certificates/` | Minimal theorem-relevant artifacts actually checked by Lean. |
| `lakefile.toml`, `lean-toolchain` | Pinned Lean project environment inherited from the Lean starter. |

`Challenge.lean` and `Solution.lean` must not import one another. Shared
statement-level definitions belong in `ProofProject/Definitions.lean`; proof
machinery belongs on the solution side.

## Minimum Lean workflow

The stages are logical safeguards, not mandatory separate Codex sessions.

1. **State the target faithfully.** Translate `PROBLEM.md` and relevant
   `../proof/` material into shared definitions and exact declarations in
   `Challenge.lean`.
2. **Prove it independently.** Give declarations with the same names and types
   in `Solution.lean`, using helper modules as needed.
3. **Check the actual proof.** Run the focused build required for the current
   work. A typical final command is:

```bash
cd lean
lake update          # only when dependencies are not already materialized
lake build Solution
```

A completed ordinary Lean deliverable has no proof-side `sorry`, `admit`,
invented axiom, or unverified external computation.

Lean proof development need not wait for a polished TeX manuscript. When the
source theorem is still being developed, Lean may help expose the right
statement and proof. Before claiming a faithful formalization, however, the
mathematical target and Lean statement must agree.

## Computer-assisted and numerical work

Exact data or CAP artifacts may be read from stable paths under `../proof/` when
mathematically necessary. External search or candidate generation is not itself
a Lean proof: the final theorem must check the relevant artifact through Lean,
a proved checker, or a sound certified-numerics interface.

`NUMERICAL_POLICY.md` and `NUMERICAL_TARGETS.md` are available for theorem-
bearing numerical claims. Use them when such claims exist; do not create
numerical bureaucracy for a purely analytic theorem.

LeanCert is imported in `ProofProject/Helpers.lean` as the default certified
numerics option in this starter. The proof strategy remains open, and its use is
not mandatory when ordinary Lean or exact reasoning is better.

## Optional enhanced verification

The following files support a stronger source-fidelity and trust-boundary audit:

| File | Purpose |
|---|---|
| `STATEMENT_AUDIT.md` | Source-to-Lean correspondence and deliberate statement lock. |
| `comparator.json` | Declarations and permitted axioms for Challenge/Solution comparison. |
| `REFEREE_STANDARDS.md` | A menu of adversarial review concerns. |
| `VERIFICATION.md` | Final verification record. |
| `formalization.yaml` | Optional provenance and formalization metadata. |
| `scripts/run_comparator.sh` | Fresh Comparator run in a copied environment. |
| `scripts/validate_formalization.sh` | Optional metadata-schema validation. |
| `scripts/verify.sh` | Runs both optional final checks. |

These are not automatic prerequisites for exploratory or ordinary Lean proof
development. Use them when the Goal asks for publication-grade verification,
when source fidelity is a major risk, or when the completion criterion explicitly
requires the Challenge/Solution comparison.

The Comparator script expects a non-root Linux environment with the external
Comparator, `landrun`, and a compatible `lean4export` executable available. It
copies the repository into a fresh temporary workspace while preserving the
sibling `proof/` and `lean/` layout. Follow the current official tool
documentation before relying on the final run.

## Toolchain changes

The shipped pins come from the supplied Lean starter. Change Lean, LeanCert, or
Mathlib deliberately, preferably before treating the statement environment as
locked. A toolchain change after a final statement audit may require rechecking
elaboration and fidelity, but do not build an upgrade framework around this.

Generated `.lake/`, `.olean`, `.ilean`, and temporary verification files are
ignored by Git. Commit `lake-manifest.json` once the actual project has a chosen,
working dependency graph.

## Project record

Codex may replace this section with a concise status summary when useful:

- **Source theorem:** `PROBLEM.md` and relevant files in `../proof/`
- **Main Lean declarations:** `ProofProject.replace_me_after_statement_lock`
- **Statement status:** uninitialized
- **Proof status:** not started
- **Enhanced verification:** not requested or not run
