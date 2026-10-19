import NLA.Proofs.TR14.GraphListContext
import NLA.Proofs.TR14.GraphBlockModeDimension
import NLA.Proofs.TR14.ScalarGraphSeparation
import NLA.Proofs.TR14.CornerInheritance
import NLA.Proofs.TR14.OrthogonalBlockDimensions
import NLA.Proofs.TR14.LocalBlockSupport
import NLA.Proofs.TR14.NumericalBlockLower
import NLA.Proofs.TR14.FrobeniusMinimal

/-! The unrestricted ordinary lower bound for an actual normalized least
apolar quotient. Every ordinary width witness is allowed. Actual minimum
summands, normalized graph spaces, reduced primitive blocks, mode image
ranks and dimension partitions are constructed by proved support gates.
There is no dimension/width restriction or supplied lower-bound oracle. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.TR14
open NLA.Statements.TR14
noncomputable section

/-- Full ordinary lower bound in successor mode dimension. The same monic
least apolar quotient used by both symmetric upper constructions is kept. -/
theorem ordinary_lower_of_minimal_monic_succ {m q w : ℕ}
    (hm : 3 ≤ m) (hq : 1 ≤ q)
    (h : Fin (m * q + 1) → ℂ) (hh : h ≠ 0) (g : Polynomial ℂ)
    (hg : g.Monic) (hrPos : 1 ≤ g.natDegree) (hrD : g.natDegree ≤ m * q)
    (hrHi : g.natDegree ≤ m * q / 2 + 1)
    (hAp : IsApolar h g.natDegree hrD (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (hmin : ∀ d : ℕ, ∀ hd : d ≤ m * q, d < g.natDegree →
      ∀ b : Fin (d + 1) → ℂ, IsApolar h d hd b → b = 0)
    (hw : OrdinaryWidth (Hankel (m := m) (n := q + 1) h) w) :
    min (m * q - g.natDegree + 2)
      ((m - 1) * g.natDegree - (m - 2) * (localRootSupport g).card) ≤ w := by
  classical
  let : Module.Finite ℂ (AdjoinRoot g) := hg.finite_adjoinRoot
  obtain ⟨R, hRw, hR, hRmin⟩ := exists_minimal_ordinaryWidth hw
  obtain ⟨u, hu⟩ := hR
  have hcoord : ∀ i, Hankel (m := m) (n := q + 1) h i = ∑ j, ordinarySummand u j i := hu
  have hind : LinearIndependent ℂ (ordinarySummand u) :=
    minimal_ordinary_summands_independent (by omega) u (Hankel (m := m) (n := q + 1) h) hcoord hRmin
  let φ := quotientModeLinear g q
  let mom := quotientMomentFunctional h g hg hrD
  have hmom : ∀ x : AdjoinRoot g, (∀ y, mom (x * y) = 0) → x = 0 :=
    quotientMomentFunctional_frobenius h hh g hg hrPos hrD hAp hmin
  have hmoment : ∀ p : Fin m → Fin (q + 1) → ℂ,
      mom (∏ k, φ (p k)) = ∑ i, Hankel (m := m) (n := q + 1) h i * ∏ k, p k (i k) := by
    intro p
    exact quotientMomentFunctional_mode_pairing_of_apolar h g hg hrD hAp p
  choose a ha using fun k : Fin m => exists_unit_mem_ordinaryGraphSpace φ
    (quotientModeLinear_one_mem_range g q) u hind k
  let L := List.ofFn (normalizedGraphSpace φ u a)
  let W := L.prod
  let Λ := normalizedGraphFunctional mom a
  have hLprod : W = ∏ k, normalizedGraphSpace φ u a k := Fin.prod_ofFn _
  have hone : ∀ U ∈ L, (1 : AdjoinRoot g × (Fin R → ℂ)) ∈ U := by
    intro U hU
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hU
    exact one_mem_normalizedGraphSpace φ u a ha k
  have hne : L ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [L, List.length_ofFn, List.length_nil] at hl
    omega
  have hFrob : ∀ x : AdjoinRoot g,
      (∀ y, Λ (x * y, 0) = 0) → x = 0 := normalizedGraphFunctional_frobenius mom hmom a
  have hann : ∀ x ∈ W, Λ x = 0 := by
    intro x hx
    rw [hLprod] at hx
    exact normalizedGraph_product_annihilated φ mom u a (Hankel (m := m) (n := q + 1) h) hcoord hmoment hx
  have hproj : ∀ i < L.length, ∀ b : AdjoinRoot g,
      ∃ x ∈ (L.take i).prod * (L.drop (i + 1)).prod, x.1 = b := by
    intro i hi b
    exact normalizedGraph_list_all_but_one_projection g hg (by omega) hrHi u a i hi b
  have honto : W.map (AlgHom.snd ℂ (AdjoinRoot g) (Fin R → ℂ)).toLinearMap = ⊤ := by
    rw [hLprod]
    exact normalizedGraph_product_snd φ u a hind
  have hscalar : ∀ j : Fin R, Λ (0, Pi.single j 1) ≠ 0 :=
    normalizedGraphFunctional_scalar_ne_zero mom a
  have hWfirst : W.map (AlgHom.fst ℂ (AdjoinRoot g) (Fin R → ℂ)).toLinearMap = ⊤ := by
    have ht := normalizedGraph_listproduct_fst_top g hg u a (List.finRange m)
      (by simpa only [List.length_finRange] using Nat.le_succ_of_le hrD)
    simpa only [W, L, List.ofFn_eq_map] using ht
  have hfirst : ∀ b : AdjoinRoot g, ∃ x ∈ W, x.1 = b := by
    intro b
    have hb : b ∈ W.map (AlgHom.fst ℂ (AdjoinRoot g) (Fin R → ℂ)).toLinearMap := by
      rw [hWfirst]
      exact Submodule.mem_top
    obtain ⟨x, hx, hxb⟩ := hb
    exact ⟨x, hx, hxb⟩
  let : IsReduced (productStabilizer W) :=
    productStabilizer_isReduced_of_context Λ W hFrob hfirst hann
  obtain ⟨t, ⟨ψ⟩⟩ := reduced_complex_exists_equiv_fin (productStabilizer W)
  let e := fun j : Fin t => reducedBlockIdempotent (productStabilizer W) ψ j
  have he (j : Fin t) : e j * e j = e j :=
    reducedBlockIdempotent_mul_self (productStabilizer W) ψ j
  have heK (j : Fin t) : e j ∈ productStabilizer W :=
    reducedBlockIdempotent_mem (productStabilizer W) ψ j
  have heA (j : Fin t) : (e j).1 ≠ 0 :=
    stabilizer_fst_ne_zero Λ W hann hscalar honto (e j) (heK j)
      (reducedBlockIdempotent_ne_zero (productStabilizer W) ψ j)
  have hcount : t ≤ (localRootSupport g).card := by
    apply orthogonal_idempotent_card_le_rootSupport g hg (fun j => (e j).1) heA
    · intro j
      exact congrArg Prod.fst (he j)
    · intro i j hij
      exact congrArg Prod.fst (reducedBlockIdempotent_mul_eq_zero (productStabilizer W) ψ hij)
  let rblock := fun j : Fin t => Module.finrank ℂ (IdempotentCorner (e j).1)
  let Rblock := fun j : Fin t => Module.finrank ℂ (IdempotentCorner (e j).2)
  have hsumr : ∑ j, rblock j = g.natDegree := by
    calc
      (∑ j, rblock j) = ∑ j, Module.finrank ℂ
          (LinearMap.range (LinearMap.mulLeft ℂ (e j).1)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact corner_finrank (K := ℂ) (e j).1 (congrArg Prod.fst (he j))
      _ = Module.finrank ℂ (AdjoinRoot g) :=
        sum_finrank_mapped_reducedBlocks (productStabilizer W) ψ
          (AlgHom.fst ℂ (AdjoinRoot g) (Fin R → ℂ))
      _ = g.natDegree := (AdjoinRoot.powerBasis' hg).finrank
  have hsumR : ∑ j, Rblock j = R := by
    calc
      (∑ j, Rblock j) = ∑ j, Module.finrank ℂ
          (LinearMap.range (LinearMap.mulLeft ℂ (e j).2)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact corner_finrank (K := ℂ) (e j).2 (congrArg Prod.snd (he j))
      _ = Module.finrank ℂ (Fin R → ℂ) :=
        sum_finrank_mapped_reducedBlocks (productStabilizer W) ψ
          (AlgHom.snd ℂ (AdjoinRoot g) (Fin R → ℂ))
      _ = R := by simp
  have hblock (j : Fin t) : m * min (q + 1) (rblock j) + 2 ≤ Rblock j + rblock j + m := by
    have hd := primitive_corner_block_dimension_inequality Λ L hne hone hFrob hann hproj ψ j
      (heA j) (min (q + 1) (rblock j)) (by
        intro U hU
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hU
        exact normalizedGraph_corner_mode_finrank_lower g hg u a (e j) (he j) k)
    simp only [L, List.length_ofFn] at hd
    change m * min (q + 1) (rblock j) + 2 ≤ rblock j + Rblock j + m at hd
    omega
  have hlower := numerical_block_lower hm (show 2 ≤ q + 1 by omega) hrD
    rblock Rblock hsumr hsumR hcount hblock
  exact hlower.trans hRw

/-- The unrestricted ordinary lower bound in the canonical mode-dimension
parameters, with all actual least-apolar hypotheses retained explicitly. -/
theorem ordinary_lower_of_minimal_monic {m n w : ℕ}
    (hm : 3 ≤ m) (hn : 2 ≤ n)
    (h : Fin (m * (n - 1) + 1) → ℂ) (hh : h ≠ 0) (g : Polynomial ℂ)
    (hg : g.Monic) (hrPos : 1 ≤ g.natDegree) (hrD : g.natDegree ≤ m * (n - 1))
    (hrHi : g.natDegree ≤ m * (n - 1) / 2 + 1)
    (hAp : IsApolar h g.natDegree hrD (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (hmin : ∀ d : ℕ, ∀ hd : d ≤ m * (n - 1), d < g.natDegree →
      ∀ b : Fin (d + 1) → ℂ, IsApolar h d hd b → b = 0)
    (hw : OrdinaryWidth (Hankel (m := m) (n := n) h) w) :
    min (m * (n - 1) - g.natDegree + 2)
      ((m - 1) * g.natDegree - (m - 2) * (localRootSupport g).card) ≤ w := by
  cases n with
  | zero => omega
  | succ q =>
    exact ordinary_lower_of_minimal_monic_succ hm (by omega) h hh g hg hrPos hrD hrHi hAp hmin hw

#assert_trust kernel ordinary_lower_of_minimal_monic_succ
#assert_trust kernel ordinary_lower_of_minimal_monic
#print axioms ordinary_lower_of_minimal_monic_succ
#print axioms ordinary_lower_of_minimal_monic

end
end NLA.Proofs.TR14
