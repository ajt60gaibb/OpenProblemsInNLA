# Upstream references

This template summarizes rather than vendors the upstream projects. Consult their current official documentation before installing or invoking external verification tools.

## LeanCert

- Repository: https://github.com/alerad/leancert
- Shipped release: see the `rev` line in `lakefile.toml`
- Documentation: https://docs.leancert.io/

LeanCert provides certified numerical tactics and APIs for inequalities, interval bounds, roots, optimization, finite sums, and integrals. For future upgrades, choose a stable LeanCert release and copy its matching Lean toolchain rather than mixing independent versions. The current pins live only in `lean-toolchain` and `lakefile.toml`.

## Comparator

- Repository: https://github.com/leanprover/comparator

Comparator builds and exports separate `Challenge` and `Solution` modules, compares configured statements, checks permitted axioms, and replays the solution through Lean's kernel. Follow its current README for `landrun`, compatible `lean4export`, sandbox, and non-root requirements.

## formalization.yaml

- Repository: https://github.com/mathlib-initiative/formalization.yaml
- Schema version: see the `version` field in `formalization.yaml`

The root metadata file records provenance, intent, automation, fidelity, review, and the Comparator configuration without duplicating information already mechanically present in the Lean repository. The validator uses the upstream dispatcher, so a future schema upgrade is localized to `formalization.yaml` and any schema-specific wording.

## Tau Ceti review standards

- Project: https://github.com/TauCetiProject/TauCeti
- Review runner and rubrics: https://github.com/TauCetiProject/TauCetiReview

Tau Ceti uses multiple adversarial AI review rubrics, including correctness, reuse, API design, generality, naming, documentation, and proof quality. `REFEREE_STANDARDS.md` adapts the relevant parts for a standalone proof project rather than importing Tau Ceti's full pull-request machinery.
