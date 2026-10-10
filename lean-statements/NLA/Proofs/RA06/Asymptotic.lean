import NLA.Statements.RA06
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Cast

/-! Numerical asymptotics used by the finite complete-graph obstruction for RA-06. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Filter

namespace NLA.Proofs.RA06

/-- A positive real power eventually dominates any positive multiple of a
positive power of a logarithm, even after a fixed polynomial change in the
logarithm's argument. -/
theorem eventually_log_polynomial_lt_power
    (s c K a : ℝ) (hs : 0 < s) (hc : 0 < c) (hK : 0 < K) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop,
      K * Real.rpow (Real.log (32 * Real.rpow x a)) c < Real.rpow x s := by
  let D := K * Real.rpow (1 + a) c
  have hD : 0 < D := mul_pos hK (Real.rpow_pos_of_pos (by linarith : 0 < 1 + a) c)
  have hsmall := (isLittleO_log_rpow_rpow_atTop c hs).bound
    (show 0 < (2 * D)⁻¹ by positivity)
  filter_upwards [hsmall, eventually_ge_atTop (32 : ℝ)] with x hsmall hx
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlog32 : Real.log 32 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have harg0 : 0 < 32 * Real.rpow x a :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hx0 a)
  have hlogarg : Real.log (32 * Real.rpow x a) ≤
      (1 + a) * Real.log x := by
    rw [Real.rpow_eq_pow, Real.log_mul (by norm_num : (32 : ℝ) ≠ 0)
      (ne_of_gt (Real.rpow_pos_of_pos hx0 a)), Real.log_rpow hx0]
    nlinarith
  have hlogarg0 : 0 ≤ Real.log (32 * Real.rpow x a) := by
    apply Real.log_nonneg
    have hxa : 1 ≤ Real.rpow x a := Real.one_le_rpow (by linarith : 1 ≤ x) ha.le
    nlinarith
  have hpow : Real.rpow (Real.log (32 * Real.rpow x a)) c ≤
      Real.rpow (1 + a) c * Real.rpow (Real.log x) c := by
    calc
      _ ≤ Real.rpow ((1 + a) * Real.log x) c :=
        Real.rpow_le_rpow hlogarg0 hlogarg hc.le
      _ = _ := Real.mul_rpow (by linarith) hlog0
  have hsmall' : Real.rpow (Real.log x) c ≤ (2 * D)⁻¹ * Real.rpow x s := by
    simpa only [Real.rpow_eq_pow, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlog0 c),
      abs_of_nonneg (Real.rpow_nonneg hx0.le s)] using hsmall
  have hxs : 0 < Real.rpow x s := Real.rpow_pos_of_pos hx0 s
  have hmul : D * Real.rpow (Real.log x) c ≤ (1 / 2 : ℝ) * Real.rpow x s := by
    calc
      _ ≤ D * ((2 * D)⁻¹ * Real.rpow x s) := mul_le_mul_of_nonneg_left hsmall' hD.le
      _ = _ := by field_simp [ne_of_gt hD]
  have hfirst : K * Real.rpow (Real.log (32 * Real.rpow x a)) c ≤
      D * Real.rpow (Real.log x) c := by
    calc
      _ ≤ K * (Real.rpow (1 + a) c * Real.rpow (Real.log x) c) :=
        mul_le_mul_of_nonneg_left hpow hK.le
      _ = _ := by ring
  linarith

/-- A natural-number witness for the exact power/log separation required by
the complete-graph counterexample. -/
theorem exists_large_accuracy_parameter
    (p C c : ℝ) (hp : 2 < p) (hC : 0 < C) (hc : 0 < c) :
    ∃ b : ℕ, 3 ≤ b ∧
      C * (Real.rpow 2 (p - 2) + 1) *
          Real.rpow (Real.log (32 * Real.rpow (b : ℝ) (3 * p + 7))) c <
        Real.rpow 6 (-p) / 3 * Real.rpow (b : ℝ) (p - 2) := by
  have hs : 0 < p - 2 := by linarith
  have ha : 0 < 3 * p + 7 := by linarith
  have h6 : 0 < Real.rpow 6 (-p) := Real.rpow_pos_of_pos (by norm_num) _
  let K := 3 * C * (Real.rpow 2 (p - 2) + 1) / Real.rpow 6 (-p)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hevent := eventually_log_polynomial_lt_power (p - 2) c K (3 * p + 7)
    hs hc hK ha
  have hnat : ∀ᶠ b : ℕ in atTop,
      K * Real.rpow (Real.log (32 * Real.rpow (b : ℝ) (3 * p + 7))) c <
        Real.rpow (b : ℝ) (p - 2) :=
    tendsto_natCast_atTop_atTop.eventually hevent
  obtain ⟨N, hN⟩ := eventually_atTop.1 hnat
  let b := max N 3
  refine ⟨b, le_max_right _ _, ?_⟩
  have hb := hN b (le_max_left _ _)
  dsimp [K] at hb
  have hden : Real.rpow 6 (-p) ≠ 0 := ne_of_gt h6
  have hmul := mul_lt_mul_of_pos_left hb h6
  dsimp [K] at hmul
  field_simp [hden] at hmul
  have hmul' : 3 * C * (Real.rpow 2 (p - 2) + 1) *
      Real.rpow (Real.log (32 * Real.rpow (b : ℝ) (3 * p + 7))) c <
      Real.rpow 6 (-p) * Real.rpow (b : ℝ) (p - 2) := by
    simpa only [Real.rpow_eq_pow, mul_comm p 3] using hmul
  nlinarith

/-- The real dimension threshold follows already from `b ≥ 3`; a graph
with `v ≥ b^(p+2)` consequently has enough vertices for the support bound. -/
theorem accuracy_parameter_dimension_regime
    (p b : ℝ) (hp : 2 < p) (hb : 3 ≤ b) :
    Real.rpow 6 (-p) * Real.rpow b (p + 1) + 1 ≤
      Real.rpow b (p + 2) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hpow : 1 ≤ Real.rpow b (p + 1) :=
    Real.one_le_rpow hb1 (by linarith)
  have h6 : Real.rpow 6 (-p) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hpowid : Real.rpow b (p + 2) = b * Real.rpow b (p + 1) := by
    calc
      Real.rpow b (p + 2) = Real.rpow b ((p + 1) + 1) := by congr 1; ring
      _ = Real.rpow b (p + 1) * b := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_add hb0, Real.rpow_one]
      _ = _ := by ring
  rw [hpowid]
  nlinarith [mul_nonneg (by linarith : 0 ≤ b - 2) (le_trans zero_le_one hpow)]

/-- The finite graph bridge needs only these two size estimates, with the
same `v`, `S`, and expected size `E`. This is a conditional numerical
contradiction, independent of the exact RA-06 target proposition. -/
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
      Real.rpow (Real.log (32 * Real.rpow (b : ℝ) (3 * p + 7))) c) : False := by
  let B : ℝ := b
  let L : ℝ := Real.rpow (Real.log (32 * Real.rpow B (3 * p + 7))) c
  let Q : ℝ := Real.rpow 2 (p - 2) + 1
  let R : ℝ := Real.rpow 6 (-p) / 3
  have hB : 0 < B := by dsimp [B]; exact_mod_cast (show 0 < b by omega)
  have hBsq : 0 < B^2 := sq_pos_of_pos hB
  have harg : 1 ≤ 32 * Real.rpow B (3 * p + 7) := by
    have hpow : 1 ≤ Real.rpow B (3 * p + 7) :=
      Real.one_le_rpow (by dsimp [B]; exact_mod_cast (show 1 ≤ b by omega))
        (by linarith)
    nlinarith
  have hL : 0 ≤ L :=
    Real.rpow_nonneg (Real.log_nonneg harg) c
  have hscale : 0 ≤ C * B^2 * L := by positivity
  have hpower : Real.rpow B p = Real.rpow B (p - 2) * B^2 := by
    calc
      Real.rpow B p = Real.rpow B ((p - 2) + 2) := by congr 1; ring
      _ = Real.rpow B (p - 2) * Real.rpow B 2 := Real.rpow_add hB _ _
      _ = _ := by simp only [Real.rpow_eq_pow, Real.rpow_two]
  have hbudget : E ≤ (v * B^2) * (C * Q * L) := by
    calc
      E ≤ C * B^2 * S * L := hEupper
      _ = (C * B^2 * L) * S := by ring
      _ ≤ (C * B^2 * L) * (Q * v) := mul_le_mul_of_nonneg_left hS hscale
      _ = (v * B^2) * (C * Q * L) := by ring
  have hstrict : (v * B^2) * (C * Q * L) <
      (v * B^2) * (R * Real.rpow B (p - 2)) :=
    mul_lt_mul_of_pos_left hsep (mul_pos hv hBsq)
  have hlower' : (v * B^2) * (R * Real.rpow B (p - 2)) ≤ E := by
    calc
      _ = R * v * Real.rpow B p := by rw [hpower]; ring
      _ ≤ E := hElower
  exact (not_le_of_gt (lt_of_le_of_lt hbudget hstrict)) hlower'

/-- Uniform power/log separation with independently supplied positive
coefficients for the graph size upper and lower estimates. -/
theorem exists_large_accuracy_parameter_for_coefficients
    (p C c L K : ℝ)
    (hp : 2 < p) (hC : 0 < C) (hc : 0 < c) (hL : 0 < L) (hK : 0 < K) :
    ∃ b : ℕ, 3 ≤ b ∧
      C * K * Real.rpow (Real.log
          (32 * Real.rpow (b : ℝ) (3 * p + 7))) c <
        L * Real.rpow (b : ℝ) (p - 2) := by
  let D := C * K / L
  have hD : 0 < D := div_pos (mul_pos hC hK) hL
  have hs : 0 < p - 2 := by linarith
  have ha : 0 < 3 * p + 7 := by linarith
  have hevent := eventually_log_polynomial_lt_power (p - 2) c D (3 * p + 7)
    hs hc hD ha
  have hnat : ∀ᶠ b : ℕ in atTop,
      D * Real.rpow (Real.log (32 * Real.rpow (b : ℝ) (3 * p + 7))) c <
        Real.rpow (b : ℝ) (p - 2) :=
    tendsto_natCast_atTop_atTop.eventually hevent
  obtain ⟨N, hN⟩ := eventually_atTop.1 hnat
  let b := max N 3
  refine ⟨b, le_max_right _ _, ?_⟩
  have hb := hN b (le_max_left _ _)
  have hscaled := mul_lt_mul_of_pos_left hb hL
  dsimp [D] at hscaled
  have hLne : L ≠ 0 := ne_of_gt hL
  field_simp [hLne] at hscaled
  simpa only [Real.rpow_eq_pow] using hscaled

/-- Conditional numerical contradiction for the arbitrary-weight support
route. In particular, `L` may include a fixed `1-δ` factor. -/
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
      Real.rpow (Real.log (32 * Real.rpow (b : ℝ) (3 * p + 7))) c) : False := by
  let B : ℝ := b
  let Q : ℝ := Real.rpow (Real.log (32 * Real.rpow B (3 * p + 7))) c
  have hB : 0 < B := by dsimp [B]; exact_mod_cast (show 0 < b by omega)
  have hBsq : 0 < B^2 := sq_pos_of_pos hB
  have harg : 1 ≤ 32 * Real.rpow B (3 * p + 7) := by
    have hpow : 1 ≤ Real.rpow B (3 * p + 7) :=
      Real.one_le_rpow (by dsimp [B]; exact_mod_cast (show 1 ≤ b by omega))
        (by linarith)
    nlinarith
  have hQ : 0 ≤ Q := Real.rpow_nonneg (Real.log_nonneg harg) c
  have hscale : 0 ≤ C * B^2 * Q := by positivity
  have hpower : Real.rpow B p = Real.rpow B (p - 2) * B^2 := by
    calc
      Real.rpow B p = Real.rpow B ((p - 2) + 2) := by congr 1; ring
      _ = Real.rpow B (p - 2) * Real.rpow B 2 := Real.rpow_add hB _ _
      _ = _ := by simp only [Real.rpow_eq_pow, Real.rpow_two]
  have hbudget : E ≤ (v * B^2) * (C * K * Q) := by
    calc
      E ≤ C * B^2 * S * Q := hEupper
      _ = (C * B^2 * Q) * S := by ring
      _ ≤ (C * B^2 * Q) * (K * v) := mul_le_mul_of_nonneg_left hS hscale
      _ = (v * B^2) * (C * K * Q) := by ring
  have hstrict : (v * B^2) * (C * K * Q) <
      (v * B^2) * (L * Real.rpow B (p - 2)) :=
    mul_lt_mul_of_pos_left hsep (mul_pos hv hBsq)
  have hlower' : (v * B^2) * (L * Real.rpow B (p - 2)) ≤ E := by
    calc
      _ = L * v * Real.rpow B p := by rw [hpower]; ring
      _ ≤ E := hElower
  exact (not_le_of_gt (lt_of_le_of_lt hbudget hstrict)) hlower'

/-- The logarithmic argument for the complete graph is bounded using only
the upper half of the ceiling estimate. The left argument is
`8 b * binom(v,2) * (v-1)` after expanding `binom(v,2)`. -/
theorem completeGraph_log_upper_of_ceiling_bound
    (p b v : ℝ) (hp : 2 < p) (hb : 3 ≤ b) (hv : 3 ≤ v)
    (hceil : v ≤ Real.rpow b (p + 2) + 1) :
    Real.log (4 * b * v * (v - 1)^2) ≤
      Real.log (32 * Real.rpow b (3 * p + 7)) := by
  let t := Real.rpow b (p + 2)
  have hb0 : 0 < b := by linarith
  have ht0 : 0 < t := Real.rpow_pos_of_pos hb0 _
  have ht1 : 1 ≤ t := Real.one_le_rpow (by linarith) (by linarith)
  have hv0 : 0 < v := by linarith
  have hvm1 : 0 ≤ v - 1 := by linarith
  have hvle : v ≤ 2 * t := by linarith
  have hvm1le : v - 1 ≤ t := by linarith
  have hsq : (v - 1)^2 ≤ t^2 := by gcongr
  have hraw : 4 * b * v * (v - 1)^2 ≤ 8 * b * t^3 := by
    calc
      4 * b * v * (v - 1)^2 ≤ 4 * b * (2 * t) * t^2 := by
        gcongr
      _ = 8 * b * t^3 := by ring
  have hcube : (Real.rpow b (p + 2))^3 = Real.rpow b ((p + 2) * 3) := by
    simpa only [Real.rpow_eq_pow, Nat.cast_ofNat] using
      (Real.rpow_mul_natCast hb0.le (p + 2) 3).symm
  have hpowid : b * t^3 = Real.rpow b (3 * p + 7) := by
    calc
      b * t^3 = Real.rpow b 1 * (Real.rpow b (p + 2))^3 := by
        simp [t, Real.rpow_one]
      _ = Real.rpow b 1 * Real.rpow b ((p + 2) * 3) := by rw [hcube]
      _ = Real.rpow b (3 * p + 7) := by
        calc
          _ = Real.rpow b (1 + (p + 2) * 3) := by
            simpa only [Real.rpow_eq_pow] using
              (Real.rpow_add hb0 1 ((p + 2) * 3)).symm
          _ = _ := by congr 1; ring
  have harg : 4 * b * v * (v - 1)^2 ≤
      32 * Real.rpow b (3 * p + 7) := by
    rw [← hpowid]
    nlinarith [mul_pos hb0 (pow_pos ht0 3)]
  have hleft : 0 < 4 * b * v * (v - 1)^2 := by
    have : 0 < v - 1 := by linarith
    positivity
  exact Real.log_le_log hleft harg

/-- A log bound usable when the graph proof only has the coarse estimates
`n ≤ v²` and `d ≤ v`. The raw target argument at `ε=1/b`, `δ=1/4` is
`8*b*n*d`. -/
theorem budget_log_upper_of_coarse_graph_bounds
    (p b v n d : ℝ) (hp : 2 < p) (hb : 3 ≤ b)
    (hv : 0 < v) (hn : 0 < n) (hd : 0 < d)
    (hceil : v ≤ Real.rpow b (p + 2) + 1)
    (hcount : n ≤ v^2) (hdim : d ≤ v) :
    Real.log (8 * b * n * d) ≤
      Real.log (32 * Real.rpow b (3 * p + 7)) := by
  let t := Real.rpow b (p + 2)
  have hb0 : 0 < b := by linarith
  have ht0 : 0 < t := Real.rpow_pos_of_pos hb0 _
  have ht2 : 2 ≤ t := by
    have hbpower : b ≤ t := by
      dsimp [t]
      simpa only [Real.rpow_eq_pow, Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le
          (by linarith : 1 ≤ b) (by linarith : (1 : ℝ) ≤ p + 2))
    have ht3 : 3 ≤ t := hb.trans hbpower
    linarith
  have hvle : v ≤ (3 / 2 : ℝ) * t := by linarith
  have hnd : n * d ≤ v^3 := by
    calc
      n * d ≤ v^2 * d := mul_le_mul_of_nonneg_right hcount hd.le
      _ ≤ v^2 * v := mul_le_mul_of_nonneg_left hdim (sq_nonneg v)
      _ = v^3 := by ring
  have hvcube : v^3 ≤ ((3 / 2 : ℝ) * t)^3 := by gcongr
  have hraw : 8 * b * n * d ≤ 27 * b * t^3 := by
    calc
      8 * b * n * d = (8 * b) * (n * d) := by ring
      _ ≤ (8 * b) * v^3 := mul_le_mul_of_nonneg_left hnd (by positivity)
      _ ≤ (8 * b) * ((3 / 2 : ℝ) * t)^3 :=
        mul_le_mul_of_nonneg_left hvcube (by positivity)
      _ = 27 * b * t^3 := by ring
  have hpowid : b * t^3 = Real.rpow b (3 * p + 7) := by
    have hcube : (Real.rpow b (p + 2))^3 = Real.rpow b ((p + 2) * 3) := by
      simpa only [Real.rpow_eq_pow, Nat.cast_ofNat] using
        (Real.rpow_mul_natCast hb0.le (p + 2) 3).symm
    calc
      b * t^3 = Real.rpow b 1 * (Real.rpow b (p + 2))^3 := by
        simp [t, Real.rpow_one]
      _ = Real.rpow b 1 * Real.rpow b ((p + 2) * 3) := by rw [hcube]
      _ = Real.rpow b (3 * p + 7) := by
        calc
          _ = Real.rpow b (1 + (p + 2) * 3) := by
            simpa only [Real.rpow_eq_pow] using
              (Real.rpow_add hb0 1 ((p + 2) * 3)).symm
          _ = _ := by congr 1; ring
  have harg : 8 * b * n * d ≤ 32 * Real.rpow b (3 * p + 7) := by
    rw [← hpowid]
    nlinarith [mul_pos hb0 (pow_pos ht0 3)]
  exact Real.log_le_log (by positivity) harg

/-- The same logarithmic estimate with the original budget argument at
`ε = 1/b`, `δ = 1/4`, before simplifying its denominator. -/
theorem budget_log_upper_of_coarse_graph_bounds_raw
    (p b v n d : ℝ) (hp : 2 < p) (hb : 3 ≤ b)
    (hv : 0 < v) (hn : 0 < n) (hd : 0 < d)
    (hceil : v ≤ Real.rpow b (p + 2) + 1)
    (hcount : n ≤ v^2) (hdim : d ≤ v) :
    Real.log (2 * n * d / ((1 / b) * (1 / 4))) ≤
      Real.log (32 * Real.rpow b (3 * p + 7)) := by
  have hb0 : b ≠ 0 := ne_of_gt (by linarith : 0 < b)
  have harg : 2 * n * d / ((1 / b) * (1 / 4)) = 8 * b * n * d := by
    field_simp [hb0]
    ring
  rw [harg]
  exact budget_log_upper_of_coarse_graph_bounds p b v n d hp hb hv hn hd
    hceil hcount hdim

/-- The exact complete-graph budget logarithm for the stated ceiling choice
of vertex count. This uses the real cast of the exact binomial edge count. -/
theorem completeGraph_budget_log_upper_for_ceiling
    (p : ℝ) (b v : ℕ) (hp : 2 < p) (hb : 3 ≤ b)
    (hvceil : v = Nat.ceil (Real.rpow (b : ℝ) (p + 2))) :
    Real.log (2 * (v.choose 2 : ℝ) * ((v - 1 : ℕ) : ℝ) /
      ((1 / (b : ℝ)) * (1 / 4))) ≤
      Real.log (32 * Real.rpow (b : ℝ) (3 * p + 7)) := by
  let B : ℝ := b
  let t := Real.rpow B (p + 2)
  have hB : 3 ≤ B := by dsimp [B]; exact_mod_cast hb
  have hB1 : 1 ≤ B := by linarith
  have ht0 : 0 < t := Real.rpow_pos_of_pos (by linarith : 0 < B) _
  have hBt : B ≤ t := by
    dsimp [t]
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith : (1 : ℝ) ≤ p + 2))
  have ht3 : 3 ≤ t := hB.trans hBt
  have hv3R : (3 : ℝ) ≤ (v : ℝ) := by
    rw [hvceil]
    exact ht3.trans (Nat.le_ceil t)
  have hv3 : 3 ≤ v := by exact_mod_cast hv3R
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (show 0 < v by omega)
  have hnpos : 0 < (v.choose 2 : ℝ) := by
    exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ v))
  have hdpos : 0 < ((v - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < v - 1 by omega)
  have hceil : (v : ℝ) ≤ t + 1 := by
    rw [hvceil]
    exact (Nat.ceil_lt_add_one ht0.le).le
  have hcount : (v.choose 2 : ℝ) ≤ (v : ℝ)^2 := by
    rw [Nat.cast_choose_two]
    nlinarith [sq_nonneg (v : ℝ)]
  have hdim : ((v - 1 : ℕ) : ℝ) ≤ (v : ℝ) := by
    exact_mod_cast Nat.sub_le v 1
  exact budget_log_upper_of_coarse_graph_bounds_raw p B v
    (v.choose 2 : ℝ) ((v - 1 : ℕ) : ℝ) hp hB hvpos hnpos hdpos
    hceil hcount hdim

/-- Budget log bound for a finite edge set whose cardinality is only known
to be at most `v*v`. This is the interface used by the grounded graph
matrix, where the edge count is `Fintype.card (Edge v)`. -/
theorem budget_log_upper_for_ceiling_card_bound
    (p : ℝ) (b v n : ℕ) (hp : 2 < p) (hb : 3 ≤ b)
    (hvceil : v = Nat.ceil (Real.rpow (b : ℝ) (p + 2)))
    (hnpos : 0 < n) (hcount : n ≤ v * v) :
    Real.log (2 * (n : ℝ) * ((v - 1 : ℕ) : ℝ) /
      ((1 / (b : ℝ)) * (1 / 4))) ≤
      Real.log (32 * Real.rpow (b : ℝ) (3 * p + 7)) := by
  let B : ℝ := b
  let t := Real.rpow B (p + 2)
  have hB : 3 ≤ B := by dsimp [B]; exact_mod_cast hb
  have hB1 : 1 ≤ B := by linarith
  have ht0 : 0 < t := Real.rpow_pos_of_pos (by linarith : 0 < B) _
  have hBt : B ≤ t := by
    dsimp [t]
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith : (1 : ℝ) ≤ p + 2))
  have ht3 : 3 ≤ t := hB.trans hBt
  have hv3R : (3 : ℝ) ≤ (v : ℝ) := by
    rw [hvceil]
    exact ht3.trans (Nat.le_ceil t)
  have hv3 : 3 ≤ v := by exact_mod_cast hv3R
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (show 0 < v by omega)
  have hnposR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hdpos : 0 < ((v - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < v - 1 by omega)
  have hceil : (v : ℝ) ≤ t + 1 := by
    rw [hvceil]
    exact (Nat.ceil_lt_add_one ht0.le).le
  have hcountR : (n : ℝ) ≤ (v : ℝ)^2 := by
    have h : (n : ℝ) ≤ (v : ℝ) * (v : ℝ) := by exact_mod_cast hcount
    nlinarith
  have hdim : ((v - 1 : ℕ) : ℝ) ≤ (v : ℝ) := by
    exact_mod_cast Nat.sub_le v 1
  exact budget_log_upper_of_coarse_graph_bounds_raw p B v
    (n : ℝ) ((v - 1 : ℕ) : ℝ) hp hB hvpos hnposR hdpos
    hceil hcountR hdim

#print axioms eventually_log_polynomial_lt_power
#print axioms exists_large_accuracy_parameter
#print axioms accuracy_parameter_dimension_regime
#print axioms finite_bounds_contradict_power_log_separation
#print axioms exists_large_accuracy_parameter_for_coefficients
#print axioms finite_bounds_contradict_for_coefficients
#print axioms completeGraph_log_upper_of_ceiling_bound
#print axioms budget_log_upper_of_coarse_graph_bounds
#print axioms budget_log_upper_of_coarse_graph_bounds_raw
#print axioms completeGraph_budget_log_upper_for_ceiling
#print axioms budget_log_upper_for_ceiling_card_bound
#assert_trust kernel eventually_log_polynomial_lt_power
#assert_trust kernel exists_large_accuracy_parameter
#assert_trust kernel accuracy_parameter_dimension_regime
#assert_trust kernel finite_bounds_contradict_power_log_separation
#assert_trust kernel exists_large_accuracy_parameter_for_coefficients
#assert_trust kernel finite_bounds_contradict_for_coefficients
#assert_trust kernel completeGraph_log_upper_of_ceiling_bound
#assert_trust kernel budget_log_upper_of_coarse_graph_bounds
#assert_trust kernel budget_log_upper_of_coarse_graph_bounds_raw
#assert_trust kernel completeGraph_budget_log_upper_for_ceiling
#assert_trust kernel budget_log_upper_for_ceiling_card_bound

end NLA.Proofs.RA06
