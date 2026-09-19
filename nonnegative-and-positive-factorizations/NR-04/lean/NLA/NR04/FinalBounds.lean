/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Exact frozen NR-04 C13-C15 from Matthew J. Colbrook's mathematical proof,
University of Cambridge. The seven-term reflection upper certificate retains
its Hrubeš / Gillis--Glineur mathematical attribution in the source manuscript.
The ordinary rank certificate consumes the kernel-mode LeanCert numerical
obligation. The lower bound is for all real nonnegative factors, not a bounded
search or a rational-only certificate. Challenge is not imported.
-/
import NLA.NR04.GeneralLowerBound
import NLA.NR04.ReflectionCertificate
import NLA.NR04.OrdinaryRank

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.NR04

theorem nine_point_no_small_factor :
    ∀ k : ℕ, k ≤ 6 → ¬ HasNonnegativeFactorization distanceNine k := by
  exact general_rank_seven_lower distanceNine (by decide) distance_rank_certificate.2
    distance_sign_pattern.2.1 distance_sign_pattern.2.2

theorem nine_point_nonnegative_rank_seven :
    IsLeast {k : ℕ | HasNonnegativeFactorization distanceNine k} 7 := by
  constructor
  · exact ⟨upperW, upperH, seven_factor_certificate⟩
  · intro k hk
    change HasNonnegativeFactorization distanceNine k at hk
    by_contra h
    have hk6 : k ≤ 6 := by omega
    exact nine_point_no_small_factor k hk6 hk

theorem canonical_six_factor_impossible :
    ¬ ∃ W : Matrix (Fin 9) (Fin 6) ℝ,
      ∃ H : Matrix (Fin 6) (Fin 9) ℝ,
        (∀ i j, 0 ≤ W i j) ∧ (∀ i j, 0 ≤ H i j) ∧
          W * H = distanceNine := by
  rintro ⟨W, H, hW, hH, hWH⟩
  exact nine_point_no_small_factor 6 (by decide) ⟨W, H, hW, hH, hWH⟩

#print axioms nine_point_no_small_factor
#print axioms nine_point_nonnegative_rank_seven
#print axioms canonical_six_factor_impossible
#assert_trust kernel nine_point_no_small_factor
#assert_trust kernel nine_point_nonnegative_rank_seven
#assert_trust kernel canonical_six_factor_impossible

end NLA.NR04
