/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.IE14.WitnessEntries
import NLA.IE14.ColumnBounds

noncomputable section
open scoped BigOperators NNReal
namespace NLA.IE14

theorem entryMax_pos_of_path {n : ℕ} (hn : 1 ≤ n) (A : Mat n)
    (path : PivotPath n) (hp : AdmissiblePath A path) : 0 < entryMax A := by
  let z : Fin n := ⟨0,by omega⟩
  have hz : A (path z) z ≠ 0 := by simpa [z,trajectory] using (hp z).2.1
  exact lt_of_lt_of_le (norm_pos_iff.mpr hz) (norm_le_entryMax A (path z) z)

theorem cyclic_growth_bound (n : ℕ) (hn : 4 ≤ n) (A : Mat n)
    (hA : CyclicInput A) (path : PivotPath n) (hp : AdmissiblePath A path) :
    growth A path ≤ fibonacciBound n := by
  have hE := entryMax_pos_of_path (by omega) A path hp
  change peakMax A path / entryMax A ≤ fibonacciBound n
  apply (div_le_iff₀ hE).mpr
  apply peakMax_le _ _ _ (mul_nonneg (by unfold fibonacciBound; positivity) hE.le)
  intro k
  apply activeMax_le _ _ _ (mul_nonneg (by unfold fibonacciBound; positivity) hE.le)
  intro i j hi hj
  exact all_active_entries_bound_proved n hn A hA path hp k i j hi hj

theorem witness_attainment_proved (n : ℕ) (hn : 4 ≤ n) :
    AdmissiblePath (witnessMatrix n hn) (witnessPath n hn) ∧
      growth (witnessMatrix n hn) (witnessPath n hn)=fibonacciBound n := by
  have hd := witness_data_proved n hn
  have hp := witness_path_admissible n hn
  refine ⟨hp, le_antisymm (cyclic_growth_bound n hn _ hd.1 _ hp) ?_⟩
  change fibonacciBound n ≤ peakMax (witnessMatrix n hn) (witnessPath n hn) /
    entryMax (witnessMatrix n hn)
  rw [hd.2,div_one]
  let k : Fin n := ⟨n-1,by omega⟩
  have hentry := norm_le_activeMax
    (trajectory (witnessMatrix n hn) (witnessPath n hn) (n-1)) (n-1) k k le_rfl le_rfl
  rw [witness_final_scalar n hn] at hentry
  have hnorm : ‖(Nat.fib (n+1) : ℂ)+1‖ = fibonacciBound n := by
    have hc : (Nat.fib (n+1) : ℂ)+1 = (fibonacciBound n : ℂ) := by
      simp [fibonacciBound]
    rw [hc,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ fibonacciBound n by unfold fibonacciBound; positivity)]
  rw [hnorm] at hentry
  exact hentry.trans (activeMax_le_peakMax _ _ k)

theorem canonical_result_proved (n : ℕ) (hn : 4 ≤ n) :
    IsGreatest (cyclicGrowthSet n) (fibonacciBound n) ∧
      sharpConstant n=fibonacciBound n := by
  have hd := witness_data_proved n hn
  have hp := witness_attainment_proved n hn
  have hg : IsGreatest (cyclicGrowthSet n) (fibonacciBound n) := by
    constructor
    · exact ⟨witnessMatrix n hn,witnessPath n hn,hd.1,hp.1,hp.2.symm⟩
    · rintro r ⟨A,path,hA,hpath,rfl⟩
      exact cyclic_growth_bound n hn A hA path hpath
  exact ⟨hg,hg.isLUB.csSup_eq ⟨_,hg.1⟩⟩

end NLA.IE14
