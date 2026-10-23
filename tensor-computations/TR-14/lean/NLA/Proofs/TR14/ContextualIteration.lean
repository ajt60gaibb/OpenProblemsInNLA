import NLA.Proofs.TR14.ContextualProduct

/-! Iterating the actual contextual product inequality along a nonempty list.
All-but-one projections are specified at actual list positions. Every prefix
stabilizer acts on the final product, giving the final stabilizer dimension
as a common upper bound. No trivial-stabilizer or block existence is assumed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

variable {A C : Type*} [CommRing A] [CommRing C] [Algebra ℂ A] [Algebra ℂ C]

/-- A product of one-containing actual subspaces contains one, also for an
empty product (the scalar subspace). -/
theorem one_mem_list_submodule_prod (L : List (Submodule ℂ (A × C)))
    (hL : ∀ U ∈ L, (1 : A × C) ∈ U) : (1 : A × C) ∈ L.prod := by
  induction L with
  | nil => exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  | cons U L ih =>
      simpa only [List.prod_cons, one_mul] using
        Submodule.mul_mem_mul (hL U (by simp)) (ih (fun V hV => hL V (by simp [hV])))

variable [IsReduced C] [FiniteDimensional ℂ A] [FiniteDimensional ℂ C]

/-- The sum-of-dimensions form of the contextual inequality for a nonempty
actual product. The stabilizer term is computed from that same final product. -/
theorem contextual_product_list_dimension_bound
    (Λ : (A × C) →ₗ[ℂ] ℂ) (L : List (Submodule ℂ (A × C)))
    (hne : L ≠ []) (hone : ∀ U ∈ L, (1 : A × C) ∈ U)
    (hFrob : ∀ a : A, (∀ b : A, Λ (a * b, 0) = 0) → a = 0)
    (hann : ∀ w ∈ L.prod, Λ w = 0)
    (hproj : ∀ i < L.length, ∀ b : A,
      ∃ x ∈ (L.take i).prod * (L.drop (i + 1)).prod, x.1 = b) :
    (L.map (fun U : Submodule ℂ (A × C) => Module.finrank ℂ U)).sum ≤ Module.finrank ℂ L.prod +
      (L.length - 1) * Module.finrank ℂ (productStabilizer L.prod) := by
  let d := Module.finrank ℂ (productStabilizer L.prod)
  have step (P : List (Submodule ℂ (A × C))) (U : Submodule ℂ (A × C))
      (Q : List (Submodule ℂ (A × C))) (hL : L = P ++ U :: Q) :
      Module.finrank ℂ P.prod + Module.finrank ℂ U ≤
        Module.finrank ℂ (P ++ [U]).prod + d := by
    have hUone : (1 : A × C) ∈ U := hone U (by simp [hL])
    have hPone : (1 : A × C) ∈ P.prod :=
      one_mem_list_submodule_prod P (fun V hV => hone V (by simp [hL, hV]))
    have hprojection : ∀ b : A, ∃ x ∈ P.prod * Q.prod, x.1 = b := by
      have hi : P.length < L.length := by simp [hL]
      simpa [hL] using hproj P.length hi
    have heq : (U * P.prod) * Q.prod = L.prod := by
      simp [hL, mul_left_comm, mul_assoc]
    have hd := contextual_product_step Λ U P.prod Q.prod L.prod hUone hPone
      hFrob hprojection hann (le_of_eq heq)
    have hst : productStabilizer (U * P.prod) ≤ productStabilizer L.prod := by
      rw [← heq]
      exact productStabilizer_le_mul_right (U * P.prod) Q.prod
    have hstdim := Submodule.finrank_mono (show
      (productStabilizer (U * P.prod)).toSubmodule ≤
        (productStabilizer L.prod).toSubmodule from hst)
    change Module.finrank ℂ (productStabilizer (U * P.prod)) ≤ d at hstdim
    have heq' : (P ++ [U]).prod = U * P.prod := by simp [mul_comm]
    rw [heq']
    omega
  have extend : ∀ (Q P : List (Submodule ℂ (A × C))), L = P ++ Q → P ≠ [] →
      (P.map (fun U : Submodule ℂ (A × C) => Module.finrank ℂ U)).sum ≤ Module.finrank ℂ P.prod +
        (P.length - 1) * d →
      (L.map (fun U : Submodule ℂ (A × C) => Module.finrank ℂ U)).sum ≤ Module.finrank ℂ L.prod +
        (L.length - 1) * d := by
    intro Q
    induction Q with
    | nil =>
        intro P hLP _ hbound
        have hPL : P = L := by simpa only [List.append_nil] using hLP.symm
        subst P
        exact hbound
    | cons U Q ih =>
        intro P hLP hP hbound
        have hd := step P U Q hLP
        have hlen : 1 ≤ P.length := List.length_pos_iff.mpr hP
        have hcoeff : (P.length - 1) * d + d = P.length * d := by
          calc
            (P.length - 1) * d + d = ((P.length - 1) + 1) * d := by
              rw [Nat.add_mul, Nat.one_mul]
            _ = P.length * d := by congr 1; omega
        have hnext : ((P ++ [U]).map (fun V : Submodule ℂ (A × C) => Module.finrank ℂ V)).sum ≤
            Module.finrank ℂ (P ++ [U]).prod + ((P ++ [U]).length - 1) * d := by
          simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
            List.sum_cons, List.sum_nil, Nat.add_zero, List.length_append, List.length_cons,
            List.length_nil, Nat.add_sub_cancel]
          omega
        apply ih (P ++ [U]) (by simpa using hLP) (by simp) hnext
  cases L with
  | nil => exact (hne rfl).elim
  | cons U Q =>
      apply extend Q [U] (by simp) (by simp)
      have hdU : Module.finrank ℂ ([U] : List (Submodule ℂ (A × C))).prod =
          Module.finrank ℂ U := by
        exact congrArg (fun T : Submodule ℂ (A × C) => Module.finrank ℂ T)
          (by simp)
      simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.add_zero, List.length_cons, List.length_nil, Nat.sub_self,
        Nat.zero_mul, hdU] using (le_refl (Module.finrank ℂ U))

/-- With at most one scalar dimension in the actual final stabilizer, the
usual trivial-stabilizer dimension bound follows. -/
theorem contextual_product_list_dimension_bound_of_stabilizer_finrank_le_one
    (Λ : (A × C) →ₗ[ℂ] ℂ) (L : List (Submodule ℂ (A × C)))
    (hne : L ≠ []) (hone : ∀ U ∈ L, (1 : A × C) ∈ U)
    (hFrob : ∀ a : A, (∀ b : A, Λ (a * b, 0) = 0) → a = 0)
    (hann : ∀ w ∈ L.prod, Λ w = 0)
    (hproj : ∀ i < L.length, ∀ b : A,
      ∃ x ∈ (L.take i).prod * (L.drop (i + 1)).prod, x.1 = b)
    (hstab : Module.finrank ℂ (productStabilizer L.prod) ≤ 1) :
    (L.map (fun U : Submodule ℂ (A × C) => Module.finrank ℂ U)).sum ≤
      Module.finrank ℂ L.prod + (L.length - 1) := by
  have h := contextual_product_list_dimension_bound Λ L hne hone hFrob hann hproj
  have hd := Nat.mul_le_mul_left (L.length - 1) hstab
  simp only [Nat.mul_one] at hd
  omega

#assert_trust kernel one_mem_list_submodule_prod
#assert_trust kernel contextual_product_list_dimension_bound
#assert_trust kernel contextual_product_list_dimension_bound_of_stabilizer_finrank_le_one
#print axioms contextual_product_list_dimension_bound_of_stabilizer_finrank_le_one

end NLA.Proofs.TR14
