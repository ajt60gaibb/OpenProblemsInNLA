# Independent referee standards

These standards collect adversarial questions that are useful for a serious Lean review. They do not prescribe the proof-search strategy, and ordinary development need not run every lane or create five reports. Select the lanes that address the live risk; use independent agents for multiple lanes when the Goal requests a final high-assurance audit or when independence materially improves confidence.

A reviewer may issue one of:

- `APPROVE` — no material issue found;
- `CHANGES_REQUESTED` — specific fixable material issues;
- `BLOCK` — the formalization cannot honestly be accepted without returning to an earlier gate.

A report must distinguish correctness risks from optional polish and cite exact declarations or files.

## Referee 1 — Source fidelity and correctness

Act as if a formally accepted but semantically wrong theorem is the principal failure mode.

Check:

- exact correspondence between `../proof/` and `ProofProject/Definitions.lean` / `Challenge.lean`;
- quantifiers, implication direction, hypotheses, domains, coercions, conventions, and edge cases;
- whether the statement is weaker, vacuous, circular, or made easy by an impossible assumption;
- whether difficulty has merely been moved into an unproved definition, typeclass, imported assumption, or literature dependency;
- whether `Solution.lean` proves the configured declaration rather than a nearby result.

Try concrete edge cases and countermodels when useful. A green Lean build is not evidence of source fidelity.

## Referee 2 — Numerical certification and computational scope

Check every item in `NUMERICAL_TARGETS.md` against `../proof/` and the Lean statement.

Check:

- constants, units, normalization, inequality directions, strictness, endpoints, and variable domains;
- whether interval boxes are the smallest justified domains;
- whether symbolic reduction, monotonicity, symmetry, convexity, scaling, or endpoint reduction could remove computation;
- whether the LeanCert call certifies exactly the needed residual and is reused rather than repeated;
- whether Taylor depth, subdivision, finite enumeration, or certificate size is larger than necessary;
- LeanCert trust mode and every extra trust dependency;
- whether external candidate generation is separated from Lean-checked verification.

Flag unnecessarily broad computation when it materially harms auditability, trust, or reproducibility. Do not reject a sound proof merely because a more elegant reduction may exist.

## Referee 3 — Reuse, generality, and trusted API

Search Mathlib and LeanCert before accepting new infrastructure.

Check:

- duplicate definitions or lemmas that should reuse existing declarations;
- assumptions that are unused, unnaturally strong, or chosen only to make the proof easy;
- needless overspecialization or speculative overgeneralization;
- whether statement-level definitions form a minimal, coherent trusted interface;
- whether proof-only helpers leaked into `ProofProject/Definitions.lean`;
- whether names and theorem shapes follow normal Lean/Mathlib conventions.

The goal is the natural level of generality for this project, not maximal abstraction.

## Referee 4 — Proof quality, robustness, naming, and documentation

Check:

- no unresolved `sorry`, `admit`, custom proof axiom, unsafe shortcut, or opaque trust gap on the proof side;
- proof steps are readable enough to audit and robust enough not to depend on accidental simplifier behavior;
- long or repeated reasoning is factored into meaningful lemmas;
- `change`, `show`, coercion manipulation, and numerical transformations are documented where their purpose is not obvious;
- public names describe their conclusions without overclaiming;
- module and declaration documentation accurately state scope and limitations.

Prefer stable library tactics and explicit mathematical structure over brittle rewrite scripts.

## Referee 5 — Comparator and trust boundary

Review the project as an adversarial statement/solution comparison.

Check:

- `Challenge.lean` and `Solution.lean` do not import one another;
- all configured theorem names occur with exactly matching types;
- every declaration used in target statements comes from the trusted shared definitions/import closure;
- no Comparator definition holes are used unless separately justified and reviewed;
- `comparator.json` lists every result claimed by the project and permits no unnecessary axiom;
- trusted files were not silently modified during proof work;
- every mechanically consumed file from `../proof/` is documented and remains available in the copied sibling layout;
- the final Comparator run occurs in the fresh environment created by the supplied script;
- `VERIFICATION.md` does not overstate what Comparator guarantees.

## Coordinator

For a multi-lane final audit, a coordinator should synthesize only after the selected independent reviews are complete, resolve material findings, and rerun affected checks when informative. A referee's approval is evidence of review, not a substitute for Lean's kernel or any Comparator run required by the Goal.
