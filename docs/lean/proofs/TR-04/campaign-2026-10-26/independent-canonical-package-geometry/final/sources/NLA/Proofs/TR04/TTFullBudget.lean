import NLA.Proofs.TR04.TTRecursiveBudget

/-! Arithmetic envelopes used after composing the actual controller costs.
The constants are fixed before every original shape, rank tuple and tensor. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
namespace NLA.Proofs.TR04

theorem ttFullBudget_power_step (size exponent : ℕ) :
    (size+1)^exponent≤(size+1)^(exponent+1) := by
  calc
    (size+1)^exponent=(size+1)^exponent*1 := by omega
    _≤(size+1)^exponent*(size+1) := Nat.mul_le_mul_left _ (by omega)
    _=(size+1)^(exponent+1) := (pow_succ _ _).symm

theorem ttFullBudget_candidate (size depth : ℕ) (hd : depth≤size) :
    24*(size+1)^2+(3000*depth*ttRecursiveUnit size+2000*ttRecursiveUnit size)+
      18*(size+1)≤8000*(size+1)^4 := by
  have h2 : (size+1)^2≤(size+1)^4 :=
    (ttFullBudget_power_step size 2).trans (ttFullBudget_power_step size 3)
  have h3 : ttRecursiveUnit size≤(size+1)^4 := ttFullBudget_power_step size 3
  have h1 : size+1≤(size+1)^4 := Nat.le_self_pow (by decide) _
  have hdepth : depth*ttRecursiveUnit size≤(size+1)^4 := by
    calc
      depth*ttRecursiveUnit size≤(size+1)*ttRecursiveUnit size := Nat.mul_le_mul_right _ (by omega)
      _=(size+1)^4 := by unfold ttRecursiveUnit;ring
  nlinarith

theorem ttFullBudget_total_shifted (size candidates : ℕ) (hc : candidates≤size) :
    1024*(size+1)^3+candidates*(8000*(size+1)^4)+300*(size+1)^2≤10000*(size+1)^5 := by
  have h3 : (size+1)^3≤(size+1)^5 :=
    (ttFullBudget_power_step size 3).trans (ttFullBudget_power_step size 4)
  have h2 : (size+1)^2≤(size+1)^5 := (ttFullBudget_power_step size 2).trans h3
  have hcount : candidates*(size+1)^4≤(size+1)^5 := by
    calc
      candidates*(size+1)^4≤(size+1)*(size+1)^4 := Nat.mul_le_mul_right _ (by omega)
      _=(size+1)^5 := by ring
  nlinarith

theorem ttFullBudget_total (size candidates : ℕ) (hs : 1≤size) (hc : candidates≤size) :
    1024*(size+1)^3+candidates*(8000*(size+1)^4)+300*(size+1)^2≤1000000*size^5 := by
  have hshift : (size+1)^5≤32*size^5 := by
    calc
      (size+1)^5≤(2*size)^5 := Nat.pow_le_pow_left (by omega) 5
      _=32*size^5 := by ring
  calc
    _≤10000*(size+1)^5 := ttFullBudget_total_shifted size candidates hc
    _≤10000*(32*size^5) := Nat.mul_le_mul_left 10000 hshift
    _=320000*size^5 := by ring
    _≤1000000*size^5 := Nat.mul_le_mul_right _ (by decide)

#assert_trust kernel ttFullBudget_power_step
#assert_trust kernel ttFullBudget_candidate
#assert_trust kernel ttFullBudget_total_shifted
#assert_trust kernel ttFullBudget_total
#print axioms ttFullBudget_total
end NLA.Proofs.TR04
