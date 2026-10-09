# Independent review of full-proof contracts

Date: 2026-10-06.

The root coordinator independently read the centered Section 4–5 contracts in full-proof-specification.md (core draft SHA-256 9513746ae2ef82ff84548dfb987ed7d273069e823ad7078acd285e760937b9a0) and approved their mathematical statements before implementation. Approval explicitly retains:

- A6's positive singular-value denominator and valid-index guards;
- positive integer rank parameters;
- almost-everywhere full-rank guards before pseudoinverse reciprocal identities;
- stagewise conditioning rather than conditioning on success at all stages;
- constants chosen uniformly before the parameters they must control.

The independent mathematical reviewer separately approved the same centered contracts and requested one indexing clarification: the first t completed pivots and E_t,T_t depend on the first t columns, whereas selecting the zero-based pivot k uses the first k+1 columns. This correction has been made.

This is approval of exact contracts and source correspondence, not an independent proof audit of every external source theorem. No analytic contract is thereby a Lean theorem.

The subsequently proposed A4-min replacement was independently approved by both the root coordinator and the mathematical reviewer. The zero-Frobenius case is separate, finite Jensen uses normalized nonzero columns, and no independence among projections is assumed. The Gaussian convex-shift theorem remains a substantive obligation. No A4-min implementation was started by the source-analysis agent.\n\nThe restricted scalar cost route h(d) ≤ 6√(log n), for d ≥ ceil√(log n) and log n ≥ 256, was also approved before implementation by both reviewers. It suffices for the full unchanged final rate at r=ceil√(log n). See scalar-recurrence-review.md for its exact finite definitions and implemented contracts; this route does not assert the sharper arbitrary-r bound from Proposition 5.5.
