Source: CONTRIBUTING.md at base 5830ed4fb06da0659414a3deb2a40ad327aca052. Full source SHA256 df81332de8240a0daa8576b5eccc8fcce7dde88204355342b3a8890b95d67db3

## Lean verification

For in-repository formalizations, follow the [per-problem Lean workflow](docs/lean/README.md)
and [independent referee protocol](docs/lean/REVIEW.md). Shared scripts select
changed projects, validate their manifests, and run the pinned Linux checker.

Use `**Status:** Lean verified` only for a complete resolution of the original
target with reviewed Lean verification evidence. `Solved` remains appropriate
for a published result or a complete argument that has passed an independent
informal audit, including an AI-agent audit. Record who or what performed that
audit and link the report; finding no mistake does not establish formal
verification or external human peer review.

For promotion to `Lean verified`, add a **Lean proof and verification evidence**
section to the canonical README containing:

1. A stable link to the proof source at an immutable revision, the Lean
   toolchain version, and pinned dependency versions (including mathlib when
   used).
2. The exact theorem declaration names and a comparison of their definitions,
   assumptions, quantifiers and conclusions with the original problem. All
   premises needed to settle the target must be proved or be assumptions
   already present in that target.
3. Reproduction commands and a dated successful verification log covering
   those declarations and their dependencies. State whether this catalog
   reran the checks or reviewed a public verification record; do not imply a
   local rerun when none occurred.
4. A transitive axiom report (for example, `#print axioms` for every target
   theorem). Accept only Lean's standard foundational axioms `propext`,
   `Classical.choice` and `Quot.sound`, or a subset. No `sorryAx`, unproved
   custom axioms, or additional trust in native execution may support the
   target theorem. A build succeeding on its own is insufficient evidence.

Lean's documentation explains [proof validation and statement matching](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
and [transitive axiom checks](https://lean-lang.org/doc/reference/latest/Axioms/).

Link this evidence from the resolution notice and [resolution archive](RESOLVED.md).
A public source and log may support the status after review; merely mentioning
a Lean formalization does not. If a source revision changes, recheck the
correspondence and verification evidence before attaching the status to it.
Lean verification of a special case, a conditional reduction or supporting
lemmas does not promote the whole problem: retain `Partially resolved` (or
`Solved` if a complete informal resolution exists) and describe the formalized
scope. Keep all IDs, paths and original targets unchanged.
