# MF-03 finite range: independent pre-proof review

**Reviewer:** `/root` (AI agent), 9 October 2026. **Verdict:** APPROVE the exact `target_through_fifteen` contract in `FINITE_RANGE_PRE_REVIEW.md` before implementation. This is a bounded theorem for orders 1–15, not the all-order MF-03 `Target`.

The proposed conclusion reproduces the frozen target's positive-order clause verbatim: a reduced normalized pair exists, and every reduced normalized pair has no denominator zero and error at most two on the entire closed complex disk of radius three. The only added hypothesis is `m≤15`, visibly in the theorem signature. The lower endpoint `1` and upper endpoint `15` are inclusive.

For order one, `order_one_target_clause` already proves both conjuncts. For each order 2–15, its exact normalized certificate supplies a chosen pair and disk bound. The independently reviewed generic `normalized_exists_reduced` lemma turns that normalized pair into a reduced normalized pair without changing the rational function, proving existence. `disk_bound_for_every_reduced_pair` transports the chosen certificate's disk estimate to **every** reduced normalized pair of that same order. This argument does not need the chosen certificate itself to be coprime, nor does it drop the universal quantifier. Finite case analysis over the fifteen natural numbers establishes the displayed theorem; it does not infer anything at order 16 or above.

The private witness constants in the certificate modules occur in the public theorem types. Lean can infer them as implicit polynomial arguments when applying a generic helper; this is an elaboration matter and does not change the mathematical contract. The proposed source hashes match the currently frozen statement, reduction, transport and finite certificate modules. A final Lean source and kernel audit is still required after implementation.

**Reviewed contract SHA-256:** `026f12f8ac3c180e482bbb05088c72c2c5d212650568b8350cb39f10db0cb814`.
