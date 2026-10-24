/-
Copyright (c) 2026. Released under Apache 2.0 license.
Actual real summand jets of complex point derivations on the radius algebra.
-/
import NLA.Proofs.TR06.GraphProjectionDerivation
import NLA.Proofs.TR06.UnramifiedDifferentialRealJet
import NLA.Proofs.TR06.ModelNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR06.GraphProjection
open NLA.TR06 NLA.TR06.Segre GraphAlgebra GraphCharacter
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

def pivotHom (q₀ : Fin r → TensorIndex d n) :
    MvPolynomial (Coordinate q₀) ℂ →ₐ[ℂ] Source q₀ :=
  (sourceHom q₀).comp (MvPolynomial.rename Sum.inl)

def direction (q₀ : Fin r → TensorIndex d n) (δ : Source q₀ →ₗ[ℂ] ℂ)
    (L : ℂ →ₗ[ℝ] ℝ) : Parameter ℝ q₀ :=
  WithLp.toLp 2 (fun c => L (δ (sourceHom q₀ (MvPolynomial.X (Sum.inl c)))))

lemma map_real_factorPolynomial (q₀ : Fin r → TensorIndex d n) (i : Fin r)
    (j : Fin d) (u : Fin (n j)) :
    MvPolynomial.map Complex.ofRealHom (factorPolynomial ℝ q₀ i j u) =
      factorPolynomial ℂ q₀ i j u := by
  unfold factorPolynomial
  split_ifs <;> simp

lemma map_real_summandPolynomial (q₀ : Fin r → TensorIndex d n) (i : Fin r)
    (q : TensorIndex d n) :
    MvPolynomial.map Complex.ofRealHom (summandPolynomial ℝ q₀ i q) =
      summandPolynomial ℂ q₀ i q := by
  simp only [summandPolynomial,map_mul,MvPolynomial.map_X,map_prod,map_real_factorPolynomial]

/-- Each summand coordinate derivative is the corresponding real linear
component of the actual complex point derivation. -/
theorem hasDerivAt_summand_of_point_derivation (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (hz : ∀ i, z ⟨i,none⟩ ≠ 0) (δ : Source q₀ →ₗ[ℂ] ℂ)
    (hmul : ∀ a b, δ (a*b) = character q₀ z hz a * δ b + character q₀ z hz b * δ a)
    (L : ℂ →ₗ[ℝ] ℝ) (i : Fin r) (q : TensorIndex d n) :
    HasDerivAt (fun t : ℝ => summands q₀ (z + t • direction q₀ δ L) i q)
      (L (δ (sourceSummand q₀ i q))) 0 := by
  have hχ (c : Coordinate q₀) : character q₀ z hz (pivotHom q₀ (MvPolynomial.X c)) =
      (z c : ℂ) := by simp [pivotHom]
  have h := hasDerivAt_real_polynomial_of_point_derivation (pivotHom q₀)
    (character q₀ z hz) δ hmul L (fun c => z c) hχ (summandPolynomial ℝ q₀ i q)
  have hf (t : ℝ) : MvPolynomial.eval
      (fun c => z c + t * L (δ (pivotHom q₀ (MvPolynomial.X c))))
      (summandPolynomial ℝ q₀ i q) = summands q₀ (z + t • direction q₀ δ L) i q := by
    have he : (fun c => z c + t * L (δ (pivotHom q₀ (MvPolynomial.X c)))) =
        (fun c => (z + t • direction q₀ δ L) c) := by
      funext c
      simp only [pivotHom,AlgHom.comp_apply,MvPolynomial.rename_X,direction,
        PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    rw [he,eval_summandPolynomial]
  have he : pivotHom q₀ (MvPolynomial.map Complex.ofRealHom
      (summandPolynomial ℝ q₀ i q)) = sourceSummand q₀ i q := by
    rw [map_real_summandPolynomial]
    rfl
  simpa only [hf,he] using h

/-- The actual radius relation holds on each real linear component. -/
theorem component_radius_relation (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (hz : ∀ i, z ⟨i,none⟩ ≠ 0) (δ : Source q₀ →ₗ[ℂ] ℂ)
    (hmul : ∀ a b, δ (a*b) = character q₀ z hz a * δ b + character q₀ z hz b * δ a)
    (L : ℂ →ₗ[ℝ] ℝ) (i : Fin r) :
    ‖summands q₀ z i‖ * L (δ (sourceRadius q₀ i)) =
      ∑ q, summands q₀ z i q * L (δ (sourceSummand q₀ i q)) := by
  have h := congrArg L (point_derivation_radius_relation q₀ z hz δ hmul i)
  simpa only [map_sum,realLinearMap_ofReal_mul] using h

/-- The infinitesimal radius prescribed by the algebra is the derivative of
the actual positive Euclidean norm, proved from its actual squared norm. -/
theorem hasDerivAt_radius_of_point_derivation (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (hz : ∀ i, z ⟨i,none⟩ ≠ 0) (δ : Source q₀ →ₗ[ℂ] ℂ)
    (hmul : ∀ a b, δ (a*b) = character q₀ z hz a * δ b + character q₀ z hz b * δ a)
    (L : ℂ →ₗ[ℝ] ℝ) (i : Fin r) :
    HasDerivAt (fun t : ℝ => ‖summands q₀ (z + t • direction q₀ δ L) i‖)
      (L (δ (sourceRadius q₀ i))) 0 := by
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun q _ =>
    (hasDerivAt_summand_of_point_derivation q₀ z hz δ hmul L i q).pow 2)
  have hf : (fun t : ℝ => ∑ q, (summands q₀ (z+t•direction q₀ δ L) i q)^2) =
      (fun t : ℝ => ‖summands q₀ (z+t•direction q₀ δ L) i‖^2) := by
    funext t
    exact (EuclideanSpace.real_norm_sq_eq _).symm
  simp only [Pi.pow_apply] at hs
  rw [hf] at hs
  have hn : ‖summands q₀ z i‖ ≠ 0 := norm_ne_zero_iff.mpr (summands_ne_zero q₀ z hz i)
  have hs' := hs.sqrt (by simpa using pow_ne_zero 2 hn)
  have hfun : (fun t : ℝ => Real.sqrt (‖summands q₀ (z+t•direction q₀ δ L) i‖^2)) =
      (fun t : ℝ => ‖summands q₀ (z+t•direction q₀ δ L) i‖) := by
    funext t
    exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun] at hs'
  convert! hs' using 1
  norm_num only [zero_smul,add_zero,Real.sqrt_sq (norm_nonneg _),pow_one]
  have hr := component_radius_relation q₀ z hz δ hmul L i
  have hsum : (∑ q, 2 * summands q₀ z i q * L (δ (sourceSummand q₀ i q))) =
      2 * ∑ q, summands q₀ z i q * L (δ (sourceSummand q₀ i q)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hsum]
  field_simp
  nlinarith [hr]

/-- The actual normalized coordinate times its actual radius is its summand. -/
lemma graphCoordinate_mul_radius (q₀ : Fin r → TensorIndex d n) (i : Fin r)
    (q : TensorIndex d n) :
    graphCoordinate q₀ (Sum.inr (i,q)) * sourceRadius q₀ i = sourceSummand q₀ i q := by
  simp only [graphCoordinate,mul_assoc,mul_comm (sourceRadiusInverse q₀ i),
    sourceRadius_mul_inverse,mul_one]

/-- The normalized algebraic coordinate has exactly the actual real
normalization derivative in every real-linear component. -/
theorem hasDerivAt_normalized_of_point_derivation (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (hz : ∀ i, z ⟨i,none⟩ ≠ 0) (δ : Source q₀ →ₗ[ℂ] ℂ)
    (hmul : ∀ a b, δ (a*b) = character q₀ z hz a * δ b + character q₀ z hz b * δ a)
    (L : ℂ →ₗ[ℝ] ℝ) (i : Fin r) (q : TensorIndex d n) :
    HasDerivAt (fun t : ℝ => realGraphValues q₀ (z+t•direction q₀ δ L) (Sum.inr (i,q)))
      (L (δ (graphCoordinate q₀ (Sum.inr (i,q))))) 0 := by
  have ha := hasDerivAt_summand_of_point_derivation q₀ z hz δ hmul L i q
  have hr := hasDerivAt_radius_of_point_derivation q₀ z hz δ hmul L i
  have hn : ‖summands q₀ z i‖ ≠ 0 := norm_ne_zero_iff.mpr (summands_ne_zero q₀ z hz i)
  have h := congrArg δ (graphCoordinate_mul_radius q₀ i q)
  rw [hmul,character_graphCoordinate,character_source_radius] at h
  have hL := congrArg L h
  simp only [realGraphValues,map_add,realLinearMap_ofReal_mul] at hL
  have hd := ha.div hr (by simpa using hn)
  convert! hd using 1
  simp only [zero_smul,add_zero]
  field_simp [hn] at hL ⊢
  nlinarith [hL]

/-- Every actual graph-coordinate jet agrees with the corresponding real
component of the actual complex algebraic point derivation. -/
theorem hasDerivAt_graphCoordinate_of_point_derivation (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (hz : ∀ i, z ⟨i,none⟩ ≠ 0) (δ : Source q₀ →ₗ[ℂ] ℂ)
    (hmul : ∀ a b, δ (a*b) = character q₀ z hz a * δ b + character q₀ z hz b * δ a)
    (L : ℂ →ₗ[ℝ] ℝ) (c : OutputCoordinate d n r) :
    HasDerivAt (fun t : ℝ => realGraphValues q₀ (z+t•direction q₀ δ L) c)
      (L (δ (graphCoordinate q₀ c))) 0 := by
  cases c with
  | inl q =>
    have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      hasDerivAt_summand_of_point_derivation q₀ z hz δ hmul L i q)
    convert! h using 1
    · funext t
      exact map_sum (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : TensorIndex d n => ℝ) q)
        (fun i : Fin r => summands q₀ (z+t•direction q₀ δ L) i) Finset.univ
    · simp only [graphCoordinate,map_sum]
  | inr c => exact hasDerivAt_normalized_of_point_derivation q₀ z hz δ hmul L c.1 c.2

#print axioms hasDerivAt_graphCoordinate_of_point_derivation
#assert_trust kernel hasDerivAt_graphCoordinate_of_point_derivation
#print axioms hasDerivAt_summand_of_point_derivation
#print axioms hasDerivAt_radius_of_point_derivation
#assert_trust kernel hasDerivAt_summand_of_point_derivation
#assert_trust kernel hasDerivAt_radius_of_point_derivation
end NLA.Proofs.TR06.GraphProjection
