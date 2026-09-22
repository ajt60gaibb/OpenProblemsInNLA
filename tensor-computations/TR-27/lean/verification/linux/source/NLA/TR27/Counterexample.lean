/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Original mathematical counterexample and proof: Matthew J. Colbrook.
-/
import NLA.TR27.RankWitness
import NLA.TR27.BorderWitness
import NLA.TR27.SegreSemantics
import NLA.TR27.CoordinateTransport
import NLA.TR27.ProjectiveGeometry

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization
namespace NLA.TR27

theorem projective_counterexample :
    witnessVariety.Admissible ∧
    ∃ (p : ℙ ℂ Space) (q : ℙ ℂ (Space ⊗[ℂ] Space)),
      Represents witnessVector p ∧ IsTensorSquare p q ∧
      projectiveRank witnessVariety.points p = 3 ∧ borderRank witnessVariety p ≤ 2 ∧
      projectiveRank (segrePoints witnessVariety.points) q = 9 := by
  let p := Projectivization.mk ℂ witnessVector witnessVector_nonzero
  have hten := nonzero_tmul witnessVector witnessVector witnessVector_nonzero witnessVector_nonzero
  let q := Projectivization.mk ℂ (witnessVector ⊗ₜ[ℂ] witnessVector) hten
  have hp : Represents witnessVector p := represents_mk _ _
  have hq : Represents (witnessVector ⊗ₜ[ℂ] witnessVector) q := represents_mk _ _
  have hrank : projectiveRank witnessVariety.points p = 3 := by
    have hr := (rank_minima witnessVariety witness_admissible p).2.1
    have h3 := (hr 3).mp ((projective_cone_rank witnessVariety witness_admissible
      3 witnessVector witnessVector_nonzero).mpr witness_three_terms.2.2.1)
    have h2 : ¬ projectiveRank witnessVariety.points p ≤ 2 := by
      intro h
      exact witness_three_terms.2.2.2 ((projective_cone_rank witnessVariety witness_admissible
        2 witnessVector witnessVector_nonzero).mp ((hr 2).mpr h))
    omega
  have hborder : borderRank witnessVariety p ≤ 2 := by
    apply ((rank_minima witnessVariety witness_admissible p).2.2.2 2).mp
    exact (projective_affine_border witnessVariety witness_admissible
      2 witnessVector witnessVector_nonzero).mpr border_two
  have hsquare : projectiveRank (segrePoints witnessVariety.points) q = 9 := by
    have hr := (segre_rank_minimum witnessVariety witness_admissible q).2
    have h9 := (hr 9).mp ((segre_cone_rank witnessVariety witness_admissible
      9 _ q hq).mpr square_nine_terms.2)
    have h8 : ¬ projectiveRank (segrePoints witnessVariety.points) q ≤ 8 := by
      intro h
      exact square_not_eight ((segre_cone_rank witnessVariety witness_admissible
        8 _ q hq).mp ((hr 8).mpr h))
    omega
  refine ⟨witness_admissible, p, q, hp, ?_, hrank, hborder, hsquare⟩
  obtain ⟨a, ha, heq⟩ := hp
  change Represents (p.rep ⊗ₜ[ℂ] p.rep) q
  rw [heq, TensorProduct.smul_tmul_smul]
  exact (represents_smul_iff _ q (a * a) (mul_ne_zero ha ha)).mpr hq

theorem original_conjecture_false : ¬ CanonicalConjecture := by
  intro h
  obtain ⟨hX, p, q, _, hsq, hr, hb, hs⟩ := projective_counterexample
  have hlt : borderRank witnessVariety p < projectiveRank witnessVariety.points p := by omega
  have hbad := h Space witnessVariety hX p q hsq hlt
  rw [hr, hs] at hbad
  norm_num at hbad

#print axioms projective_counterexample
#print axioms original_conjecture_false
end NLA.TR27
