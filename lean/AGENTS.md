# Lean-Specific Instructions

These instructions apply to material work in `lean/`. The root `AGENTS.md`,
`PROBLEM.md`, `PROGRESS.md`, and current Goal remain authoritative.

## 1. Mathematical source and fidelity

The theorem to formalize is determined by `PROBLEM.md` together with the
relevant human-readable or computer-assisted material in `../proof/`. When no
separate source document exists, `PROBLEM.md` is the source statement.

Do not make the Lean theorem weaker, vacuous, differently quantified, or easier
by silently changing hypotheses, domains, conventions, implication directions,
endpoints, or exceptional cases. If the source is ambiguous or wrong, identify
the issue, record it in the root project state, and make a deliberate correction
rather than letting the tracks diverge.

Formalization may expose a missing lemma or even lead to a better mathematical
proof. That is productive cross-track work, not a violation of focus.

## 2. Statement side and solution side

The core layout is:

- `ProofProject/Definitions.lean` — definitions needed in the target statement;
- `Challenge.lean` — the intended theorem signatures, with deliberate `sorry`
  bodies while acting as the trusted statement side;
- `ProofProject/Helpers.lean` — proof-only lemmas, APIs, and certificate checks;
- `Solution.lean` — independent proofs of the configured target declarations.

`Challenge.lean` and `Solution.lean` must not import one another. They should
declare the same configured theorem names and types in separate environments.
Keep proof-only machinery out of the shared statement definitions.

This separation is a correctness safeguard, not a mandate for three isolated
sessions. Statement clarification, exploratory Lean proof, and mathematical
work may interleave when useful. Before a final formal proof claim, however, the
intended statement must be stable and its fidelity must have been checked.

Use `STATEMENT_AUDIT.md` to preserve source-to-Lean alignment when that record is
useful or required by the completion criterion. Do not fill it ceremonially
before the statement is understood.

## 3. Proof freedom

The proof strategy is open. Search Mathlib and LeanCert, introduce good helper
lemmas, reorganize the argument, replace the informal derivation by a cleaner
equivalent proof, combine analytic reasoning with certified computation, or use
Lean to discover the right statement or decomposition.

Prefer existing library declarations when they fit. Do not contort the
mathematics merely to avoid a small local definition or helper lemma. Aim for a
natural trusted interface and auditable proof, not maximal abstraction or
minimal line count.

Temporary `sorry` may be used in exploratory files or the trusted challenge
module when it helps development. It may not remain on the proof side in a
completed Lean deliverable. Do not introduce custom axioms or unverified
external computations to manufacture completion.

## 4. Lean builds are proof work

Run the targeted Lean elaboration or build needed to know whether the current
statement or proof is accepted. `lake build Challenge`, `lake build Solution`,
focused file builds, and informative traces are not generic test overhead when
they bear on the formal proof.

Do not create CI, coverage, broad engineering test suites, or repeated full
rebuild rituals without a proof-bearing reason. Expand checking when dependency,
environment, nondeterminism, trust, or final-verification risk makes it useful.

## 5. Numerical and computer-assisted components

External programs may search for candidates, partitions, witnesses, bounds, or
certificates. Their output is untrusted until connected to the theorem through a
Lean-checked parser, checker, proof, or sound certified-numerics interface.

Use `NUMERICAL_TARGETS.md` only for nontrivial theorem-bearing numerical claims.
If none are needed, say so briefly. `NUMERICAL_POLICY.md` is guidance: reduce the
mathematics, dimensions, and domains before increasing brute-force certified
computation, but do not reject a sound computation merely because a different
proof might be more elegant.

Exact source data may be read through stable paths under `../proof/`. Document
the file and trust boundary when it actually enters the theorem. Derived Lean
code and minimal checked certificates belong in `lean/ProofProject/`.

The root individual-artifact hash policy applies. Do not hash Lean source,
`.olean` files, builds, dependencies, or directories. An exceptional stable
external certificate may be individually locked only when it satisfies the root
CAP-artifact rule.

## 6. Ordinary completion versus enhanced verification

The current Goal determines the standard.

For an ordinary Lean formalization, completion normally requires:

- the intended target is stated faithfully;
- every requested declaration has an accepted proof in `Solution.lean` or the
  appropriate solution module;
- no proof-side `sorry`, `admit`, invented axiom, or unchecked external result
  remains; and
- the relevant Lean build succeeds.

For publication-grade, challenge/solution, or independently verified work, the
repository also supplies:

- `STATEMENT_AUDIT.md` and `NUMERICAL_TARGETS.md`;
- `comparator.json` and the optional fresh Comparator runner;
- `formalization.yaml` and its optional schema validator;
- `REFEREE_STANDARDS.md` and `VERIFICATION.md`.

Use the parts that address the actual correctness risk or are required by the
completion criterion. Do not automatically run every referee lane, populate all
metadata, or install Comparator during ordinary proof development. Conversely,
do not omit them when the user explicitly requests that stronger assurance or
when a final claim relies on the challenge/solution trust boundary.

If proof development exposes a defective locked statement, return deliberately
to the statement side, record the issue, and repair it. Do not silently alter the
trusted target while claiming that the same theorem was proved.

## 7. Pro review

For Lean-focused review, `PRO_REQUEST.md` should identify the exact declarations,
source locations, and concern: statement fidelity, proof gap, library use,
certified numerics, trust boundary, or final verification. Pro may read beyond
the listed files as needed.

Pro's review is independent mathematical evidence, not a substitute for Lean's
kernel. Likewise, a successful Lean build does not by itself establish that the
formal statement matches the intended theorem.
