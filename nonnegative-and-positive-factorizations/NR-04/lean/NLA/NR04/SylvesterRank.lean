/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

The actual Sylvester inequality needed in Matthew J. Colbrook's NR-04 proof,
University of Cambridge. Rank-nullity is applied to the real linear map W
restricted to range(H); its kernel injects into the actual kernel of W.
-/
import NLA.NR04.Definitions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.NR04

/-- Sylvester's inequality for the actual matrix product, in addition form. -/
theorem matrix_sylvester_rank_bound {m n k : ℕ}
    (W : Matrix (Fin m) (Fin k) ℝ) (H : Matrix (Fin k) (Fin n) ℝ) :
    W.rank + H.rank ≤ k + (W * H).rank := by
  let f := W.mulVecLin
  let V := LinearMap.range H.mulVecLin
  let g := f.domRestrict V
  let e : LinearMap.ker g →ₗ[ℝ] LinearMap.ker f :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  have he : Function.Injective e := by
    intro x y h
    have hv : (e x).val = (e y).val :=
      congrArg (fun z : LinearMap.ker f => z.val) h
    change x.val.val = y.val.val at hv
    exact Subtype.ext (Subtype.ext hv)
  have hker := LinearMap.finrank_le_finrank_of_injective he
  have hrange : LinearMap.range g = LinearMap.range (W * H).mulVecLin := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
    exact LinearMap.range_domRestrict V f
  have hg := g.finrank_range_add_finrank_ker
  rw [hrange] at hg
  change (W * H).rank + Module.finrank ℝ (LinearMap.ker g) = H.rank at hg
  have hf := f.finrank_range_add_finrank_ker
  change W.rank + Module.finrank ℝ (LinearMap.ker f) =
    Module.finrank ℝ (Fin k → ℝ) at hf
  simp only [Module.finrank_pi, Fintype.card_fin] at hf
  omega

/-- C11: the genuine Sylvester/rank-nullity consequence used in the contradiction. -/
theorem rank_three_small_factor {m n k : ℕ}
    (W : Matrix (Fin m) (Fin k) ℝ) (H : Matrix (Fin k) (Fin n) ℝ)
    (hk : k ≤ 6) (hr : (W * H).rank = 3) :
    W.rank ≤ 4 ∨ H.rank ≤ 4 := by
  have h := matrix_sylvester_rank_bound W H
  omega

#print axioms matrix_sylvester_rank_bound
#print axioms rank_three_small_factor
#assert_trust kernel matrix_sylvester_rank_bound
#assert_trust kernel rank_three_small_factor

end NLA.NR04
