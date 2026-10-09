import Mathlib
import LeanCert.Tactic.Verification

/-! Exact scalar arithmetic for the independently reviewed Gaussian
overcrowding moment argument. No matrix probability estimate is assumed here. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open Real
open scoped BigOperators
noncomputable section
namespace NLA.IE06.GaussianOvercrowdingScalars

def momentOrder (j : ℕ) : ℕ := (j+3)/4
def minorSize (j : ℕ) : ℕ := j+1-2*momentOrder j

theorem dimensions {n j : ℕ} (hj : 4 ≤ j) (hjn : j < n) :
    1 ≤ momentOrder j ∧ 1 ≤ minorSize j ∧ minorSize j ≤ n-2*momentOrder j ∧
      2*momentOrder j + minorSize j = j+1 ∧ minorSize j ≤ j+1 := by
  dsimp [momentOrder, minorSize]
  omega

theorem exponent_bound {j : ℕ} (hj : 4 ≤ j) :
    j^2 ≤ 8 * momentOrder j * minorSize j := by
  let q := momentOrder j
  let r := minorSize j
  have hq : 1 ≤ q := by dsimp [q, momentOrder]; omega
  have hr : 2*q+r = j+1 := by dsimp [q,r,minorSize,momentOrder]; omega
  have hc : j = 4*q ∨ j+1 = 4*q ∨ j+2 = 4*q ∨ j+3 = 4*q := by
    dsimp [q, momentOrder]
    omega
  change j^2 ≤ 8*q*r
  rcases hc with h | h | h | h <;> nlinarith

theorem factorial_inverse_le {q : ℕ} (hq : 0 < q) :
    (q.factorial : ℝ)⁻¹ ≤ (exp 1 / q)^q := by
  have hqp : 0 < (q : ℝ) := by exact_mod_cast hq
  have h := Real.pow_div_factorial_le_exp (q : ℝ) hqp.le q
  have he : exp (q : ℝ) = (exp 1)^q := by simp [← Real.exp_nat_mul]
  rw [he] at h
  rw [div_pow]
  apply (le_div_iff₀ (pow_pos hqp q)).mpr
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem choose_le_exp_bound (m : ℕ) {r : ℕ} (hr : 0 < r) :
    (m.choose r : ℝ) ≤ (exp 1 * m / r)^r := by
  calc
    _ ≤ (m : ℝ)^r / r.factorial := Nat.choose_le_pow_div r m
    _ = (m : ℝ)^r * (r.factorial : ℝ)⁻¹ := div_eq_mul_inv _ _
    _ ≤ (m : ℝ)^r * (exp 1 / r)^r :=
      mul_le_mul_of_nonneg_left (factorial_inverse_le hr) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

theorem factorial_le_moment_denominator {d q : ℕ} (hd : 2*q < d) :
    (q.factorial : ℝ) ≤ ∏ a ∈ Finset.range q, ((d : ℝ)-2*(a+1)) := by
  have hf : (q.factorial : ℝ) = ∏ a ∈ Finset.range q, ((q-a : ℕ) : ℝ) := by
    rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
    have h := Finset.prod_range_reflect (fun a : ℕ => ((a+1 : ℕ) : ℝ)) q
    rw [← h]
    apply Finset.prod_congr rfl
    intro a ha
    congr 1
    have ha' := Finset.mem_range.mp ha
    omega
  rw [hf]
  apply Finset.prod_le_prod
  · intro a ha
    positivity
  · intro a ha
    have ha' := Finset.mem_range.mp ha
    rw [Nat.cast_sub (by omega : a ≤ q)]
    have hd' : 2*(q : ℝ) < d := by exact_mod_cast hd
    have ha'' : (a : ℝ) < q := by exact_mod_cast ha'
    have ha''' : (a : ℝ)+1 ≤ q := by exact_mod_cast ha'
    have hd'' : 2*(q : ℝ)+1 ≤ d := by exact_mod_cast hd
    linarith

theorem inverse_moment_denominator_le {d q : ℕ} (hq : 0 < q) (hd : 2*q < d) :
    (∏ a ∈ Finset.range q, ((d : ℝ)-2*(a+1)))⁻¹ ≤ (exp 1/q)^q := by
  have hf : 0 < (q.factorial : ℝ) := by exact_mod_cast q.factorial_pos
  exact (inv_le_inv₀ (hf.trans_le (factorial_le_moment_denominator hd)) hf).mpr
    (factorial_le_moment_denominator hd) |>.trans (factorial_inverse_le hq)

theorem scalar_threshold {n j q r : ℕ} (hn : 0 < n) (hq : 0 < q) (hr : 0 < r)
    (hqr : j^2 ≤ 8*q*r) (θ : ℝ) :
    (exp 1/q) * (exp 1*n/r) * ((j:ℝ)*θ/(4*exp 1*sqrt n))^2 ≤ θ^2 := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hqp : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrp : 0 < (r : ℝ) := by exact_mod_cast hr
  have he : (exp 1/q) * (exp 1*n/r) * ((j:ℝ)*θ/(4*exp 1*sqrt n))^2 =
      ((j:ℝ)^2/(16*q*r))*θ^2 := by
    rw [div_pow, mul_pow, mul_pow, sq_sqrt hnp.le]
    field_simp
    ring
  rw [he]
  have hjr : (j:ℝ)^2 ≤ 8*q*r := by exact_mod_cast hqr
  have hf : (j:ℝ)^2/(16*q*r) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<16*q*r)).mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_right hf (sq_nonneg θ)).trans_eq (one_mul _)

theorem moment_union_scalar {n j q r : ℕ} (hn : 0 < n) (hq : 0 < q) (hr : 0 < r)
    (hqr : j^2 ≤ 8*q*r) {N θ : ℝ} (hN : 0 ≤ N)
    (hNsharp : N ≤ (exp 1*n/r)^r) (hNcrude : N ≤ (n:ℝ)^(j+1))
    (hθ : 0 < θ) (hθone : θ ≤ 1) :
    N*(exp 1/q)^(r*q)*N^q*((j:ℝ)*θ/(4*exp 1*sqrt n))^(2*r*q) ≤
      (n:ℝ)^(j+1)*θ^((j:ℝ)^2/4) := by
  let t := (j:ℝ)*θ/(4*exp 1*sqrt n)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hb : (exp 1/q)^r*N*t^(2*r) ≤ (θ^2)^r := by
    calc
      _ ≤ (exp 1/q)^r*(exp 1*n/r)^r*t^(2*r) := by gcongr
      _ = ((exp 1/q)*(exp 1*n/r)*t^2)^r := by rw [mul_pow, mul_pow, pow_mul]
      _ ≤ (θ^2)^r := by
        apply pow_le_pow_left₀ (by positivity)
        exact scalar_threshold hn hq hr hqr θ
  have hbig : (exp 1/q)^(r*q)*N^q*t^(2*r*q) ≤ θ^(2*r*q) := by
    calc
      _ = ((exp 1/q)^r*N*t^(2*r))^q := by simp only [mul_pow, pow_mul]
      _ ≤ ((θ^2)^r)^q := pow_le_pow_left₀ (by positivity) hb q
      _ = _ := by rw [pow_mul, pow_mul]
  have hexp : θ^(2*r*q) ≤ θ^((j:ℝ)^2/4) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_ge hθ hθone
    have hjr : (j:ℝ)^2 ≤ 8*q*r := by exact_mod_cast hqr
    push_cast
    nlinarith
  calc
    _ = N*((exp 1/q)^(r*q)*N^q*t^(2*r*q)) := by dsimp [t]; ring
    _ ≤ N*θ^(2*r*q) := mul_le_mul_of_nonneg_left hbig hN
    _ ≤ (n:ℝ)^(j+1)*θ^((j:ℝ)^2/4) :=
      mul_le_mul hNcrude hexp (by positivity) (by positivity)

theorem overcrowding_scalar {n j : ℕ} (hj : 4 ≤ j) (hjn : j < n)
    {θ : ℝ} (hθ : 0 < θ) (hθone : θ ≤ 1) :
    let q := momentOrder j
    let r := minorSize j
    let N : ℝ := (n-2*q).choose r
    N*(exp 1/q)^(r*q)*N^q*((j:ℝ)*θ/(4*exp 1*sqrt n))^(2*r*q) ≤
      (n:ℝ)^(j+1)*θ^((j:ℝ)^2/4) := by
  dsimp only
  obtain ⟨hq,hr,hrm,he,hrj⟩ := dimensions hj hjn
  apply moment_union_scalar (by omega) hq hr (exponent_bound hj) (by positivity) ?_ ?_ hθ hθone
  · calc
      _ ≤ (exp 1*(n-2*momentOrder j : ℕ)/minorSize j)^minorSize j :=
        choose_le_exp_bound _ hr
      _ ≤ _ := by gcongr; exact_mod_cast Nat.sub_le n (2*momentOrder j)
  · calc
      _ ≤ ((n-2*momentOrder j : ℕ) : ℝ)^minorSize j := by
        exact_mod_cast Nat.choose_le_pow (n-2*momentOrder j) (minorSize j)
      _ ≤ (n:ℝ)^minorSize j := by gcongr; exact_mod_cast Nat.sub_le n (2*momentOrder j)
      _ ≤ (n:ℝ)^(j+1) := pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ n by omega)) hrj

#assert_trust kernel dimensions
#assert_trust kernel exponent_bound
#assert_trust kernel factorial_inverse_le
#assert_trust kernel choose_le_exp_bound
#assert_trust kernel factorial_le_moment_denominator
#assert_trust kernel inverse_moment_denominator_le
#assert_trust kernel scalar_threshold
#assert_trust kernel moment_union_scalar
#assert_trust kernel overcrowding_scalar
#print axioms dimensions
#print axioms exponent_bound
#print axioms factorial_inverse_le
#print axioms choose_le_exp_bound
#print axioms factorial_le_moment_denominator
#print axioms inverse_moment_denominator_le
#print axioms scalar_threshold
#print axioms moment_union_scalar
#print axioms overcrowding_scalar

end NLA.IE06.GaussianOvercrowdingScalars
