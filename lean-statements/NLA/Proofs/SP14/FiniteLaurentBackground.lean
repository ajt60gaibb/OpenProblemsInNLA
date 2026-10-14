import NLA.Proofs.SP14.BaseExteriorFactor

/-!
The source's finite real Laurent background on the circle, and its exact
algebraic curve/symbol identities. Wiener smallness and the conformal map
are separate analytic obligations.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- Strictly negative finite real Laurent correction. -/
noncomputable def negativeLaurent (u : ℕ) (p : Fin u → ℝ) (s : Circle) : ℂ :=
  ∑ j : Fin u, (p j : ℂ) * (s : ℂ) ^ (-((j.val + 1 : ℕ) : ℤ))

/-- Strictly positive finite real Laurent correction. -/
noncomputable def positiveLaurent (v : ℕ) (p : Fin v → ℝ) (s : Circle) : ℂ :=
  ∑ j : Fin v, (p j : ℂ) * (s : ℂ) ^ ((j.val + 1 : ℕ) : ℤ)

/-- The actual finite background correction `P₋+P₊`. -/
noncomputable def finiteLaurentCorrection (u v : ℕ)
    (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ) (s : Circle) : ℂ :=
  negativeLaurent u pMinus s + positiveLaurent v pPlus s

/-- The boundary factor `g=g₀+P₋+P₊`. -/
noncomputable def finiteBackgroundFactor (u v : ℕ)
    (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ) (s : Circle) : ℂ :=
  baseExteriorFactor s + finiteLaurentCorrection u v pMinus pPlus s

/-- The source's squared boundary curve `h(s)=s g(s)²−1`. -/
noncomputable def finiteBackgroundCurve (u v : ℕ)
    (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ) (s : Circle) : ℂ :=
  (s : ℂ) * finiteBackgroundFactor u v pMinus pPlus s ^ 2 - 1

/-- The source's corrected symbol `a(z)=z g(z²)`. -/
noncomputable def finiteBackgroundSymbol (u v : ℕ)
    (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ) (z : Circle) : ℂ :=
  (z : ℂ) * finiteBackgroundFactor u v pMinus pPlus (z ^ 2)

private theorem continuous_circle_complex_zpow (n : ℤ) :
    Continuous (fun s : Circle => (s : ℂ) ^ n) := by
  have hp : Continuous (fun s : Circle => (s : Circle) ^ n) := continuous_zpow _
  apply (continuous_subtype_val.comp hp).congr
  intro s
  exact Circle.coe_zpow s n

theorem continuous_negativeLaurent (u : ℕ) (p : Fin u → ℝ) :
    Continuous (negativeLaurent u p) := by
  unfold negativeLaurent
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul (continuous_circle_complex_zpow _)

theorem continuous_positiveLaurent (v : ℕ) (p : Fin v → ℝ) :
    Continuous (positiveLaurent v p) := by
  unfold positiveLaurent
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul (continuous_circle_complex_zpow _)

theorem continuous_finiteLaurentCorrection (u v : ℕ)
    (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ) :
    Continuous (finiteLaurentCorrection u v pMinus pPlus) :=
  (continuous_negativeLaurent u pMinus).add (continuous_positiveLaurent v pPlus)

theorem continuous_finiteBackgroundFactor (u v : ℕ)
    (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ) :
    Continuous (finiteBackgroundFactor u v pMinus pPlus) :=
  continuous_baseExteriorFactor.add
    (continuous_finiteLaurentCorrection u v pMinus pPlus)

theorem continuous_finiteBackgroundCurve (u v : ℕ)
    (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ) :
    Continuous (finiteBackgroundCurve u v pMinus pPlus) := by
  unfold finiteBackgroundCurve
  exact (continuous_subtype_val.mul
    ((continuous_finiteBackgroundFactor u v pMinus pPlus).pow 2)).sub continuous_const

theorem continuous_finiteBackgroundSymbol (u v : ℕ)
    (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ) :
    Continuous (finiteBackgroundSymbol u v pMinus pPlus) := by
  unfold finiteBackgroundSymbol
  have hsq : Continuous (fun z : Circle => (z : Circle) ^ 2) := continuous_pow 2
  exact continuous_subtype_val.mul
    ((continuous_finiteBackgroundFactor u v pMinus pPlus).comp hsq)

theorem finiteBackgroundCurve_deviation (u v : ℕ)
    (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ) (s : Circle) :
    finiteBackgroundCurve u v pMinus pPlus s - (s : ℂ) =
      2 * (s : ℂ) * baseExteriorFactor s *
        finiteLaurentCorrection u v pMinus pPlus s +
      (s : ℂ) * finiteLaurentCorrection u v pMinus pPlus s ^ 2 := by
  have hs : (s : ℂ) ≠ 0 := Circle.coe_ne_zero s
  have hbase := baseExteriorFactor_sq s
  unfold finiteBackgroundCurve finiteBackgroundFactor
  calc
    (s : ℂ) * (baseExteriorFactor s + finiteLaurentCorrection u v pMinus pPlus s) ^ 2 -
        1 - (s : ℂ) =
        (s : ℂ) * baseExteriorFactor s ^ 2 - 1 - (s : ℂ) +
        2 * (s : ℂ) * baseExteriorFactor s * finiteLaurentCorrection u v pMinus pPlus s +
        (s : ℂ) * finiteLaurentCorrection u v pMinus pPlus s ^ 2 := by ring
    _ = _ := by
      rw [hbase]
      field_simp
      ring

theorem finiteBackgroundSymbol_eq_base_add (u v : ℕ)
    (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ) (z : Circle) :
    finiteBackgroundSymbol u v pMinus pPlus z =
      baseExteriorSymbol z +
      (z : ℂ) * negativeLaurent u pMinus (z ^ 2) +
      (z : ℂ) * positiveLaurent v pPlus (z ^ 2) := by
  rw [baseExteriorSymbol_factor]
  unfold finiteBackgroundSymbol finiteBackgroundFactor finiteLaurentCorrection
  ring

theorem finiteBackgroundFactor_at_neg_one (u v : ℕ)
    (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ)
    (hMinus : negativeLaurent u pMinus (-1 : Circle) = 0)
    (hPlus : positiveLaurent v pPlus (-1 : Circle) = 0) :
    finiteBackgroundFactor u v pMinus pPlus (-1 : Circle) = 0 := by
  simp [finiteBackgroundFactor, finiteLaurentCorrection,
    baseExteriorFactor_at_neg_one, hMinus, hPlus]

theorem finiteBackgroundCurve_at_neg_one (u v : ℕ)
    (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ)
    (hMinus : negativeLaurent u pMinus (-1 : Circle) = 0)
    (hPlus : positiveLaurent v pPlus (-1 : Circle) = 0) :
    finiteBackgroundCurve u v pMinus pPlus (-1 : Circle) = -1 := by
  rw [finiteBackgroundCurve,
    finiteBackgroundFactor_at_neg_one u v pMinus pPlus hMinus hPlus]
  ring

theorem negativeLaurent_zero (s : Circle) :
    negativeLaurent 0 Fin.elim0 s = 0 := by
  simp [negativeLaurent]

theorem positiveLaurent_zero (s : Circle) :
    positiveLaurent 0 Fin.elim0 s = 0 := by
  simp [positiveLaurent]

theorem finiteBackgroundFactor_zero (s : Circle) :
    finiteBackgroundFactor 0 0 Fin.elim0 Fin.elim0 s = baseExteriorFactor s := by
  simp [finiteBackgroundFactor, finiteLaurentCorrection,
    negativeLaurent_zero, positiveLaurent_zero]

theorem finiteBackgroundCurve_zero (s : Circle) :
    finiteBackgroundCurve 0 0 Fin.elim0 Fin.elim0 s = (s : ℂ) := by
  rw [finiteBackgroundCurve, finiteBackgroundFactor_zero,
    baseExteriorFactor_sq]
  have hs : (s : ℂ) ≠ 0 := Circle.coe_ne_zero s
  field_simp
  ring

theorem finiteBackgroundSymbol_zero (z : Circle) :
    finiteBackgroundSymbol 0 0 Fin.elim0 Fin.elim0 z = baseExteriorSymbol z := by
  rw [finiteBackgroundSymbol, finiteBackgroundFactor_zero,
    baseExteriorSymbol_factor]

/-- A nonempty source-shaped negative correction: `t(s⁻¹+s⁻²)` vanishes
separately at the contact point for every real `t`. -/
theorem negativeLaurent_two_equal_at_neg_one (t : ℝ) :
    negativeLaurent 2 (fun _ => t) (-1 : Circle) = 0 := by
  simp [negativeLaurent, Fin.sum_univ_two]

/-- A nonempty source-shaped positive correction: `r(s+s²)` vanishes
separately at the contact point for every real `r`. -/
theorem positiveLaurent_two_equal_at_neg_one (r : ℝ) :
    positiveLaurent 2 (fun _ => r) (-1 : Circle) = 0 := by
  simp [positiveLaurent, Fin.sum_univ_two]

theorem finiteBackgroundCurve_two_equal_at_neg_one (t r : ℝ) :
    finiteBackgroundCurve 2 2 (fun _ => t) (fun _ => r) (-1 : Circle) = -1 := by
  exact finiteBackgroundCurve_at_neg_one 2 2 (fun _ => t) (fun _ => r)
    (negativeLaurent_two_equal_at_neg_one t)
    (positiveLaurent_two_equal_at_neg_one r)

#assert_trust kernel continuous_finiteBackgroundCurve
#assert_trust kernel continuous_finiteBackgroundSymbol
#assert_trust kernel finiteBackgroundCurve_deviation
#assert_trust kernel finiteBackgroundSymbol_eq_base_add
#assert_trust kernel finiteBackgroundCurve_at_neg_one
#assert_trust kernel finiteBackgroundCurve_zero
#assert_trust kernel finiteBackgroundSymbol_zero
#assert_trust kernel negativeLaurent_two_equal_at_neg_one
#assert_trust kernel positiveLaurent_two_equal_at_neg_one
#assert_trust kernel finiteBackgroundCurve_two_equal_at_neg_one
#print axioms finiteBackgroundCurve_deviation

end NLA.Proofs.SP14
