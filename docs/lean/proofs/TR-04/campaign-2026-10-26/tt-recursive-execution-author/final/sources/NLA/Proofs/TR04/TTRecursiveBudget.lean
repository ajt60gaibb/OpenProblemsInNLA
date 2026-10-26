import NLA.Proofs.TR04.MachineTTStageForward

/-! Uniform arithmetic envelopes for actual per-level charges and elapsed
steps. These inequalities derive from dimensions bounded by the original
entry count; they are not assumed runtime or approximation certificates. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def ttRecursiveUnit (size : ℕ) : ℕ := (size+1)^3

theorem ttRecursiveUnit_pos (size : ℕ) : 0<ttRecursiveUnit size := by
  unfold ttRecursiveUnit
  positivity

theorem ttRecursiveUnit_linear (size : ℕ) : size+1≤ttRecursiveUnit size := by
  unfold ttRecursiveUnit
  exact Nat.le_self_pow (n:=3) (by decide) (size+1)

theorem ttRecursive_cube_three (size m q cols : ℕ) (hm : m≤size) (hq : q≤size) (hc : cols≤size) :
    (m+q+cols+1)^3≤27*ttRecursiveUnit size := by
  calc
    (m+q+cols+1)^3 ≤ (3*(size+1))^3 := Nat.pow_le_pow_left (by omega) 3
    _ = 27*ttRecursiveUnit size := by unfold ttRecursiveUnit;ring

theorem ttRecursive_cube_two (size m cols : ℕ) (hm : m≤size) (hc : cols≤size) :
    (m+cols+1)^3+3≤11*ttRecursiveUnit size := by
  have hh : (m+cols+1)^3≤8*ttRecursiveUnit size := by
    calc
      (m+cols+1)^3 ≤ (2*(size+1))^3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8*ttRecursiveUnit size := by unfold ttRecursiveUnit;ring
  have hp := ttRecursiveUnit_pos size
  omega

theorem ttRecursive_own_stage_budget (size m q cols stride : ℕ)
    (hm : m≤size) (hq : q≤size) (hc : cols≤size) (hs : stride≤size) :
    (44+17*(m+q+cols+1)^3)+1+(3*(m+q+cols+stride)+132)+22+
      17*(m+q+cols+1)^3+8+100*(size+1)≤2000*ttRecursiveUnit size := by
  have hh := ttRecursive_cube_three size m q cols hm hq hc
  have hp := ttRecursiveUnit_pos size
  have hl := ttRecursiveUnit_linear size
  omega

theorem ttRecursive_prefix_budget (size depth charge : ℕ)
    (hcharge : charge≤11*ttRecursiveUnit size) :
    charge+(3000*depth*ttRecursiveUnit size+2000*ttRecursiveUnit size)≤
      3000*(depth+1)*ttRecursiveUnit size := by
  nlinarith

#assert_trust kernel ttRecursiveUnit_pos
#assert_trust kernel ttRecursiveUnit_linear
#assert_trust kernel ttRecursive_cube_three
#assert_trust kernel ttRecursive_cube_two
#assert_trust kernel ttRecursive_own_stage_budget
#assert_trust kernel ttRecursive_prefix_budget
#print axioms ttRecursive_own_stage_budget
end NLA.Proofs.TR04
