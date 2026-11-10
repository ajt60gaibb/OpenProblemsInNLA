import NLA.IE03.Certificate.Phase16Checks
import NLA.IE03.Certificate.Phase64Checks
import NLA.IE03.Certificate.Phase256Checks
import NLA.IE03.Certificate.Phase1024Checks
import NLA.IE03.Certificate.Phase4096Checks

/-! Matias Andia's counterexample to Cryer's complete-pivoting conjecture. -/

namespace NLA.IE03

open Certificate

private theorem next_phase {n m k : ℕ} {A B C D : Entries ℝ} {g f : ℝ}
    (h : Trace n A m B g) (e : Agree (2 * (2 * m)) (double (double B)) C)
    (h' : Trace (2 * (2 * m)) C k D f) :
    Trace (2 * (2 * n)) (double (double A)) k D (max (2 * (2 * g)) f) :=
  (h.double.double.finish e).append h'

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private theorem seed_checked : seedOK stage16_0 = true := by decide +kernel
private theorem lift16_checked : liftOK 6 stage16_10 stage64_0 = true := by decide +kernel
private theorem lift64_checked : liftOK 8 stage64_16 stage256_0 = true := by decide +kernel
private theorem lift256_checked : liftOK 10 stage256_22 stage1024_0 = true := by decide +kernel
private theorem lift1024_checked : liftOK 12 stage1024_28 stage4096_0 = true := by decide +kernel

private theorem prefix16 : Trace 16 (walsh 4) 6 stage16_10.entries 4 :=
  phase16.start (seed_sound seed_checked).symm

private theorem prefix64 : Trace 64 (walsh 6) 8 stage64_16.entries 16 := by
  have h := next_phase prefix16 (lift_sound lift16_checked) phase64
  simpa only [show max (2 * (2 * 4)) (16 : ℝ) = 16 by norm_num [max_def]] using! h

private theorem prefix256 : Trace 256 (walsh 8) 10 stage256_22.entries 64 := by
  have h := next_phase prefix64 (lift_sound lift64_checked) phase256
  simpa only [show max (2 * (2 * 16)) (64 : ℝ) = 64 by norm_num [max_def]] using! h

private theorem prefix1024 : Trace 1024 (walsh 10) 12 stage1024_28.entries 256 := by
  have h := next_phase prefix256 (lift_sound lift256_checked) phase1024
  simpa only [show max (2 * (2 * 64)) (256 : ℝ) = 256 by norm_num [max_def]] using! h

private theorem prefix4096 : Trace 4096 (walsh 12) 0 stage4096_48.entries 4608 := by
  have h := next_phase prefix1024 (lift_sound lift1024_checked) phase4096
  simpa only [show max (2 * (2 * 256)) (4608 : ℝ) = 4608 by norm_num [max_def]] using! h

/-- A real Hadamard matrix of order 4096 has a complete-pivoting path with
element-growth factor 4608. -/
theorem counterexample : ∃ A : Entries ℝ, IsHadamard 4096 A ∧ CompletePath 4096 A 4608 :=
  ⟨walsh 12, walsh_hadamard 12, prefix4096.complete⟩

/-- Cryer's universal complete-pivoting assertion is false. -/
theorem cryer_false :
    ¬ (∀ (n : ℕ) (A : Entries ℝ) (g : ℝ),
      0 < n → IsHadamard n A → CompletePath n A g → g = (n : ℝ)) := by
  intro h
  obtain ⟨A, hA, hp⟩ := counterexample
  have he := h 4096 A 4608 (by decide) hA hp
  norm_num at he

end NLA.IE03
