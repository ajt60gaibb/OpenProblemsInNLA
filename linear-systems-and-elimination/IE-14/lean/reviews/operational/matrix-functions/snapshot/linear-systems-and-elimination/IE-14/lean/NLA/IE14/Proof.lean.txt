/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.IE14.Attainment
import NLA.IE14.GEPP

noncomputable section
namespace NLA.IE14

theorem numerical_bounds : (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) ≤ 1 := half_bounds_certificate

-- `entryMax_semantics` is proved directly with its reviewed signature in Basic.lean.

theorem admissible_path_exists {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) :
    ∃ path : PivotPath n, AdmissiblePath A path := admissible_path_exists_proved A hA

theorem all_active_entries_bound (n : ℕ) (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) :
    ∀ k : Fin n, ∀ i j : Fin n, k ≤ i → k ≤ j →
      ‖trajectory A path k.val i j‖ ≤ fibonacciBound n * entryMax A :=
  all_active_entries_bound_proved n hn A hA path hp

theorem witness_data (n : ℕ) (hn : 4 ≤ n) :
    CyclicInput (witnessMatrix n hn) ∧ entryMax (witnessMatrix n hn)=1 := witness_data_proved n hn

theorem witness_attainment (n : ℕ) (hn : 4 ≤ n) :
    AdmissiblePath (witnessMatrix n hn) (witnessPath n hn) ∧
      growth (witnessMatrix n hn) (witnessPath n hn)=fibonacciBound n := witness_attainment_proved n hn

theorem canonical_result (n : ℕ) (hn : 4 ≤ n) :
    IsGreatest (cyclicGrowthSet n) (fibonacciBound n) ∧
      sharpConstant n=fibonacciBound n := canonical_result_proved n hn

#assert_trust kernel numerical_bounds
#print axioms numerical_bounds
#assert_trust kernel entryMax_semantics
#print axioms entryMax_semantics
#assert_trust kernel admissible_path_exists
#print axioms admissible_path_exists
#assert_trust kernel all_active_entries_bound
#print axioms all_active_entries_bound
#assert_trust kernel witness_data
#print axioms witness_data
#assert_trust kernel witness_attainment
#print axioms witness_attainment
#assert_trust kernel canonical_result
#print axioms canonical_result

end NLA.IE14
