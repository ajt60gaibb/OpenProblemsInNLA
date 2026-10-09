import NLA.TR13.KoszulWitness
import NLA.TR13.LowerRank

noncomputable section
open scoped BigOperators
open Matrix

namespace NLA.TR13

/-- The two-spike moment sequence certifying the lower-rank polynomial. -/
def twoSpikeMoment (a s i : ℕ) : ℂ :=
  if i = a - 1 ∨ i = 2 * a + s - 1 then 1 else 0

lemma twoSpike_normalized_slice {a s : ℕ} (ha : 2 * s < a)
    (j : Fin 3) (u v : Fin a) :
    twoSpikeMoment a s (a - 1 - u.val + j.val * s + v.val) =
      ![1, spikeB a s, spikeC a s] j u v := by
  have hu := u.isLt
  have hv := v.isLt
  fin_cases j
  · have he : a - 1 - u.val + v.val = a - 1 ↔ u = v := by
      rw [Fin.ext_iff]
      omega
    have hn : a - 1 - u.val + v.val ≠ 2 * a + s - 1 := by omega
    simp [twoSpikeMoment, he, hn, Matrix.one_apply]
  · have he : a - 1 - u.val + s + v.val = a - 1 ↔ v.val + s = u.val := by omega
    have hn : a - 1 - u.val + s + v.val ≠ 2 * a + s - 1 := by omega
    simp [twoSpikeMoment, he, hn, spikeB, lowerShift]
  · have he : a - 1 - u.val + 2 * s + v.val = a - 1 ↔ v.val + 2 * s = u.val := by omega
    have hn : a - 1 - u.val + 2 * s + v.val = 2 * a + s - 1 ↔
        u.val + (a - s) = v.val := by omega
    simp only [Matrix.cons_val_two, twoSpikeMoment, Fin.reduceFinMk, he, hn, spikeC]
    by_cases h1 : v.val + 2 * s = u.val <;>
      by_cases h2 : u.val + (a - s) = v.val <;> simp [lowerShift, upperShift, h1, h2]
    omega

lemma expectedRank_odd (k n : ℕ) :
    expectedRank (2 * k + 1) n = k * (n - 1) + 1 + (n - 1) / 2 := by
  unfold expectedRank
  have he : (2 * k + 1) * (n - 1) + 2 =
      2 * (k * (n - 1) + 1) + (n - 1) := by ring
  rw [he]
  omega

/-- The source's explicit two-spike generator has enough Koszul rank for every
odd format, including binary tensors where the selected slices coincide. -/
theorem exists_hankel_koszul_witness (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    ∃ h : Moments (2 * k + 1) n,
      2 * expectedRank (2 * k + 1) n ≤
        (tensorKoszul k n (by omega) (hankel h)).rank := by
  let a := k * (n - 1) + 1
  let s := (n - 1) / 2
  have ha : 2 * s < a := by
    have hs := Nat.mul_div_le (n - 1) 2
    dsimp [a, s]
    nlinarith
  let h : Moments (2 * k + 1) n := fun i => twoSpikeMoment a s i.val
  have hslices :
      (fun j u v => h (compressedMomentIndex k n (by omega) j u v)) =
        ![1, spikeB a s, spikeC a s] := by
    funext j u v
    dsimp [h, compressedMomentIndex]
    simpa [Fin.val_rev, a, s] using twoSpike_normalized_slice ha j u v
  refine ⟨h, ?_⟩
  rw [tensorKoszul_hankel, hslices, expectedRank_odd]
  simpa only [Nat.mul_add, a, s] using spike_koszul_rank (Nat.le_of_lt ha)

/-- Generic ordinary-border lower bound, with approximating tensors permitted
in the full unstructured tensor space. -/
theorem generic_border_lower (m n : ℕ) (hm : 5 ≤ m) (hodd : Odd m) (hn : 2 ≤ n) :
    ∃ p : MvPolynomial (Fin (m * (n - 1) + 1)) ℂ, p ≠ 0 ∧
      ∀ h : Moments m n, MvPolynomial.eval h p ≠ 0 → ∀ q,
        OrdinaryBorderRankAtMost q (hankel h) → expectedRank m n ≤ q := by
  obtain ⟨k, hk⟩ := hodd
  have hmform : m = 2 * k + 1 := by omega
  subst m
  exact exists_lower_polynomial_of_witness k n (expectedRank (2 * k + 1) n)
    (by omega) (exists_hankel_koszul_witness k n (by omega) hn)

end NLA.TR13
