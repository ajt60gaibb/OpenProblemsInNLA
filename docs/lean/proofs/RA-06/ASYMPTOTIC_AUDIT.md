# RA-06 asymptotic module audit

Source: `lean-statements/NLA/Proofs/RA06/Asymptotic.lean`
SHA-256: `4d39acee6e037a457445f6908bc16c82a40bed299fd15061f6df92eb7fe5d8f1`

## Exact exports

All declarations are in `NLA.Proofs.RA06`.

```lean
theorem eventually_log_polynomial_lt_power
    (s c K a : ℝ) (hs : 0 < s) (hc : 0 < c) (hK : 0 < K) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop,
      K * Real.rpow (Real.log (32 * Real.rpow x a)) c < Real.rpow x s

theorem exists_large_accuracy_parameter
    (p C c : ℝ) (hp : 2 < p) (hC : 0 < C) (hc : 0 < c) :
    ∃ b : ℕ, 3 ≤ b ∧
      C * (Real.rpow 2 (p - 2) + 1) *
          Real.rpow (Real.log (32 * Real.rpow (b : ℝ) (3 * p + 7))) c <
        Real.rpow 6 (-p) / 3 * Real.rpow (b : ℝ) (p - 2)

theorem accuracy_parameter_dimension_regime
    (p b : ℝ) (hp : 2 < p) (hb : 3 ≤ b) :
    Real.rpow 6 (-p) * Real.rpow b (p + 1) + 1 ≤
      Real.rpow b (p + 2)

theorem finite_bounds_contradict_power_log_separation
    (p C c : ℝ) (b : ℕ) (v S E : ℝ)
    (hp : 2 < p) (hC : 0 < C) (hb : 3 ≤ b) (hv : 0 < v)
    (hsep :
      C * (Real.rpow 2 (p - 2) + 1) *
          Real.rpow (Real.log (32 * Real.rpow (b : ℝ) (3 * p + 7))) c <
        Real.rpow 6 (-p) / 3 * Real.rpow (b : ℝ) (p - 2))
    (hS : S ≤ (Real.rpow 2 (p - 2) + 1) * v)
    (hElower : Real.rpow 6 (-p) / 3 * v * Real.rpow (b : ℝ) p ≤ E)
    (hEupper : E ≤ C * (b : ℝ)^2 * S *
      Real.rpow (Real.log (32 * Real.rpow (b : ℝ) (3 * p + 7))) c) : False

theorem exists_large_accuracy_parameter_for_coefficients
    (p C c L K : ℝ)
    (hp : 2 < p) (hC : 0 < C) (hc : 0 < c) (hL : 0 < L) (hK : 0 < K) :
    ∃ b : ℕ, 3 ≤ b ∧
      C * K * Real.rpow (Real.log
          (32 * Real.rpow (b : ℝ) (3 * p + 7))) c <
        L * Real.rpow (b : ℝ) (p - 2)

theorem finite_bounds_contradict_for_coefficients
    (p C c L K : ℝ) (b : ℕ) (v S E : ℝ)
    (hp : 2 < p) (hC : 0 < C) (_hL : 0 < L) (_hK : 0 < K)
    (hb : 3 ≤ b) (hv : 0 < v)
    (hsep : C * K * Real.rpow (Real.log
        (32 * Real.rpow (b : ℝ) (3 * p + 7))) c <
      L * Real.rpow (b : ℝ) (p - 2))
    (hS : S ≤ K * v)
    (hElower : L * v * Real.rpow (b : ℝ) p ≤ E)
    (hEupper : E ≤ C * (b : ℝ)^2 * S *
      Real.rpow (Real.log (32 * Real.rpow (b : ℝ) (3 * p + 7))) c) : False

theorem completeGraph_log_upper_of_ceiling_bound
    (p b v : ℝ) (hp : 2 < p) (hb : 3 ≤ b) (hv : 3 ≤ v)
    (hceil : v ≤ Real.rpow b (p + 2) + 1) :
    Real.log (4 * b * v * (v - 1)^2) ≤
      Real.log (32 * Real.rpow b (3 * p + 7))

theorem budget_log_upper_of_coarse_graph_bounds
    (p b v n d : ℝ) (hp : 2 < p) (hb : 3 ≤ b)
    (hv : 0 < v) (hn : 0 < n) (hd : 0 < d)
    (hceil : v ≤ Real.rpow b (p + 2) + 1)
    (hcount : n ≤ v^2) (hdim : d ≤ v) :
    Real.log (8 * b * n * d) ≤
      Real.log (32 * Real.rpow b (3 * p + 7))

theorem budget_log_upper_of_coarse_graph_bounds_raw
    (p b v n d : ℝ) (hp : 2 < p) (hb : 3 ≤ b)
    (hv : 0 < v) (hn : 0 < n) (hd : 0 < d)
    (hceil : v ≤ Real.rpow b (p + 2) + 1)
    (hcount : n ≤ v^2) (hdim : d ≤ v) :
    Real.log (2 * n * d / ((1 / b) * (1 / 4))) ≤
      Real.log (32 * Real.rpow b (3 * p + 7))

theorem completeGraph_budget_log_upper_for_ceiling
    (p : ℝ) (b v : ℕ) (hp : 2 < p) (hb : 3 ≤ b)
    (hvceil : v = Nat.ceil (Real.rpow (b : ℝ) (p + 2))) :
    Real.log (2 * (v.choose 2 : ℝ) * ((v - 1 : ℕ) : ℝ) /
      ((1 / (b : ℝ)) * (1 / 4))) ≤
      Real.log (32 * Real.rpow (b : ℝ) (3 * p + 7))

theorem budget_log_upper_for_ceiling_card_bound
    (p : ℝ) (b v n : ℕ) (hp : 2 < p) (hb : 3 ≤ b)
    (hvceil : v = Nat.ceil (Real.rpow (b : ℝ) (p + 2)))
    (hnpos : 0 < n) (hcount : n ≤ v * v) :
    Real.log (2 * (n : ℝ) * ((v - 1 : ℕ) : ℝ) /
      ((1 / (b : ℝ)) * (1 / 4))) ≤
      Real.log (32 * Real.rpow (b : ℝ) (3 * p + 7))
```

The two `finite_bounds_contradict_*` theorems are **conditional
finite-bounds contradictions**. Their `hS`, `hElower`, and `hEupper`
hypotheses are the interface for the graph and sampling proof; neither
asserts `NLA.Statements.RA06.Target`. The generic version accepts any
positive `L,K`. The current graph route intends
`L = 3*6^(-p)/8` and `K = 2*2^(p-1)+1`, representing respectively the
`3/4` success factor and its proved sensitivity upper coefficient.

## Local verification

- Pinned Lean: `leanprover/lean4:v4.33.1`.
- Pinned Mathlib checkout: `0df444a360eaa60ab8c11dca51a86af692955474`.
- Pinned LeanCert checkout: `621a43d7cf21f87872392a01e874f2f1dbddc926`.
- `lake env lean NLA/Proofs/RA06/Asymptotic.lean`: passed.
- `lake build NLA.Proofs.RA06.Asymptotic`: passed (2018 jobs, most replayed).
- The file sets `leancert.trust` to `"kernel"` and uses `#assert_trust kernel`
  on each export. `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound` for each. There are no `sorry`, custom
  axioms, `native_decide`, or LeanCert numerical certificates in this module.

## Remaining connection

To prove the exact target, the graph-side development must instantiate
`S = TotalSensitivity A_v p + (d : ℝ)` and
`E = ExpectedSize A_v p α`, establish the finite support lower bound with
the success factor and the sensitivity upper bound for the **same** `α`,
and connect them to the exact quantifiers in `OriginalPositiveClaim`.
The ceiling and budget logarithm bounds are now proved here, including a
version requiring only `n ≤ v*v` for `n = Fintype.card (Edge v)`.
Independent semantic review and the full proof gate remain pending.
