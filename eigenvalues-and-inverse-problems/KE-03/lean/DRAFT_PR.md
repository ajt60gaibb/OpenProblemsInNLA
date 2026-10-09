# Proposed title

KE-03: formalize the complete randomized eigenvalue query algorithm

# Proposed draft PR body

This formalizes the entire original KE-03 problem: a concrete randomized algorithm locates a near-largest eigenvalue of any promised diagonalizable complex matrix using only exact matrix-vector queries.

`NLA.KE03.complete_query_algorithm` proves termination on every seed, at most `32768 * (1 + log(n*K)) / epsilon^2` queries, and success probability at least `99/100` for both required inequalities with the same eigenvalue. The proof includes finite-grid anti-concentration, matrix estimates, search termination, transcript reconstruction, rational circle coverage, shift selection and the eigenvalue-location argument. No mathematical cases or supporting hypotheses remain unproved.

Lean 4.33.1 and Mathlib are pinned. Local build and transitive axiom checks pass, using only `propext`, `Classical.choice`, and `Quot.sound`. The authoritative [Linux run](https://github.com/marcusdavidwebb/OpenProblemsInNLA/actions/runs/36428948274) passed fresh isolated compilation, statement comparison, permitted-axiom checks, default-kernel replay and rejection controls. Two independent nonauthor agents approved the frozen statement and the complete final proof. Logs, source hashes, correspondence and reviewer reports are included.

The mathematical resolution is credited to Matthew J. Colbrook. OpenAI Codex agents generated the Lean implementation and documentation. Independent reviews are AI-agent reviews; no external human peer review or source-author endorsement is claimed. The exact-query result does not bound total runtime, bit complexity or floating-point error.

The original target, canonical path and permanent ID are preserved. The complete verified result promotes the canonical status to `Lean verified`; the problem page, TeX/PDF, indexes and resolution archive are updated. This is a draft for contributor review.

# Submission

- Base: `ajt60gaibb/OpenProblemsInNLA`, branch `main`.
- Head: `marcusdavidwebb/OpenProblemsInNLA`, branch `codex/ke03-complete-lean`.
- Open as **Draft**, using the title and body above.

[Open the comparison](https://github.com/ajt60gaibb/OpenProblemsInNLA/compare/main...marcusdavidwebb:OpenProblemsInNLA:codex/ke03-complete-lean?expand=1)
