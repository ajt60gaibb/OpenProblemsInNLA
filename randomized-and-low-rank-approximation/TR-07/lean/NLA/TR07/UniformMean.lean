import NLA.TR07.IIDMean
import NLA.TR07.ReservoirReconstruction

/-! A uniform positive linear lower bound for the expected deletion deficiency. -/
noncomputable section
open scoped BigOperators
namespace NLA.TR07
open Law

private theorem partition_sizes {r J : ℕ} (hJ : 0 < J) (hR : 4*J ≤ r) :
    let m := r/2
    let ℓ := (r-m)/J
    m + J*ℓ ≤ r ∧ r ≤ 4*J*ℓ ∧ r ≤ 3*m ∧ ℓ ≤ r := by
  dsimp
  have hm : r/2 ≤ r := Nat.div_le_self _ _
  have hhalf : J ≤ r-r/2 := by omega
  have hℓ : 1 ≤ (r-r/2)/J := (Nat.le_div_iff_mul_le hJ).mpr (by simpa using hhalf)
  have hdiv := Nat.mul_div_le (r-r/2) J
  have hflo := Nat.lt_mul_div_succ (r-r/2) hJ
  have hJle : J ≤ J*((r-r/2)/J) := by nlinarith
  have htw : r ≤ 2*(r-r/2) := by omega
  rw [Nat.mul_add, Nat.mul_one] at hflo
  have hr4 : r ≤ 4*(J*((r-r/2)/J)) := by omega
  have hlast := Nat.div_le_self (r-r/2) J
  constructor
  · omega
  constructor
  · simpa only [Nat.mul_assoc] using hr4
  constructor
  · omega
  · omega

/-- Constants depend only on sparsity, the row-to-sample ratio bound, and the error threshold. -/
theorem uniform_expected_defect (s : ℕ) (hs : 2 ≤ s) {β η : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hη : 0 < η) :
    ∃ R : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (k n r : ℕ), R ≤ r → r ≤ k → β*(k:ℝ) ≤ r → (hn : 0 < n) →
      ∀ M : Mat k n, SignedSparse s M →
        ρ*(r:ℝ) ≤ ((@Law.uniform (Fin n) _ ⟨⟨0,hn⟩⟩).iid r).expect
          (fun x => (defect (fun j => WithLp.toLp 2 (fun i => M i (x j))) η : ℝ)) := by
  obtain ⟨L,b,hL,hb,hbudget⟩ := exists_estimator_parameters s (half_pos hη)
  let J := b*L
  have hJ : 0 < J := Nat.mul_pos hb hL
  let c := β/(8*J)
  have hJreal : (0:ℝ) < J := by exact_mod_cast hJ
  have hc : 0 < c := div_pos hβ (by positivity)
  have hc1 : c ≤ 1/2 := by
    apply (div_le_iff₀ (show (0:ℝ) < 8*J by positivity)).mpr
    have hJone : (1:ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith
  refine ⟨4*J, c^(L*b)/8, by positivity, ?_⟩
  intro k n r hR hrk hβkr hn M hM
  let p := @Law.uniform (Fin n) _ ⟨⟨0,hn⟩⟩
  let u : Fin n → Vec k := fun a => WithLp.toLp 2 (fun i => M i a)
  have hu : ∀ a, SignedVector s (u a) := fun a => hM.column a
  have hk : 0 < k := by omega
  have hs0 : 0 < s := by omega
  let m := r/2
  let ℓ := (r-m)/J
  obtain ⟨hsize,hfour,hthree,hℓr⟩ := partition_sizes hJ hR
  change m+J*ℓ ≤ r at hsize
  change r ≤ 4*J*ℓ at hfour
  change r ≤ 3*m at hthree
  change ℓ ≤ r at hℓr
  have hℓk : ℓ ≤ k := hℓr.trans hrk
  have hkreal : (0:ℝ) < k := by exact_mod_cast hk
  have hfourR : (r:ℝ) ≤ 4*(J:ℝ)*ℓ := by exact_mod_cast hfour
  have hthreeR : (r:ℝ) ≤ 3*(m:ℝ) := by exact_mod_cast hthree
  have hck : c ≤ (ℓ:ℝ)/(2*k) := by
    apply (div_le_div_iff₀ (show (0:ℝ) < 8*J by positivity) (show (0:ℝ) < 2*k by positivity)).mpr
    nlinarith
  have hprob := reservoir_success_probability p u hu hk hs0 hℓk L b hb
    (half_pos hη) hbudget hc.le hc1 hck
  have hmean := expected_defect_of_reconstruction p u hη m L b ℓ r hsize hprob
  have hpow : 0 ≤ c^(L*b) := (pow_pos hc _).le
  change c^(L*b)/8*(r:ℝ) ≤ (p.iid r).expect (fun x => (defect (fun j => u (x j)) η : ℝ))
  apply le_trans ?_ hmean
  nlinarith [mul_le_mul_of_nonneg_left hthreeR hpow]

end NLA.TR07
