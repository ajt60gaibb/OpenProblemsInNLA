import NLA.Proofs.TR04.MachineRelocation

/-! Literal finite code-bank assembly. A bank occupies a fixed consecutive
label interval. Its halt cells are left to the caller, so the already proved
return prefixes continue through ordinary finite caller instructions. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

/-- Static register and constant-pool injections; these contain no input data. -/
structure BankRegisters (P Q : Program) where
  reals : Fin P.realRegisters → Fin Q.realRegisters
  naturals : Fin (P.extraNatRegisters+1) → Fin (Q.extraNatRegisters+1)
  constants : Fin P.constantCount → Fin Q.constantCount
  reals_injective : Function.Injective reals
  naturals_injective : Function.Injective naturals
  constant_values : ∀ i,Q.constants (constants i) = P.constants i

/-- Consecutive static register frames for a bank with an empty constant pool. -/
def offsetBankRegisters (P Q : Program) (realBase naturalBase : ℕ)
    (realFits : realBase+P.realRegisters≤Q.realRegisters)
    (naturalFits : naturalBase+(P.extraNatRegisters+1)≤Q.extraNatRegisters+1)
    (noConstants : P.constantCount=0) : BankRegisters P Q where
  reals i := ⟨realBase+i.val,by have := i.isLt;omega⟩
  naturals i := ⟨naturalBase+i.val,by have := i.isLt;omega⟩
  constants i := Fin.elim0 (Fin.cast noConstants i)
  reals_injective := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    change realBase+i.val=realBase+j.val at hv
    omega
  naturals_injective := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    change naturalBase+i.val=naturalBase+j.val at hv
    omega
  constant_values := by
    intro i
    exact Fin.elim0 (Fin.cast noConstants i)

def bankLabel (P Q : Program) (base : ℕ) (fits : base+(P.extraLabels+1)≤Q.extraLabels+1)
    (label : Fin (P.extraLabels+1)) : Fin (Q.extraLabels+1) :=
  ⟨base+label.val,by have := label.isLt;omega⟩

/-- All ordinary and SVD cells are copied literally with relocated operands.
Only a local halt cell or an address outside the bank uses caller code. -/
def installCodeBank (P Q : Program) (registers : BankRegisters P Q)
    (base : ℕ) (fits : base+(P.extraLabels+1)≤Q.extraLabels+1) : Program where
  extraLabels := Q.extraLabels
  realRegisters := Q.realRegisters
  extraNatRegisters := Q.extraNatRegisters
  constantCount := Q.constantCount
  constants := Q.constants
  code label := if h : base≤label.val ∧ label.val<base+(P.extraLabels+1) then
    let localLabel : Fin (P.extraLabels+1) := ⟨label.val-base,by omega⟩
    if instructionIsHalt (P.code localLabel) then Q.code label
    else relocateInstruction (bankLabel P Q base fits) registers.reals registers.naturals
      registers.constants (P.code localLabel)
  else Q.code label

theorem installCodeBank_outside (P Q : Program) (registers : BankRegisters P Q)
    (base : ℕ) (fits : base+(P.extraLabels+1)≤Q.extraLabels+1)
    (label : Fin (Q.extraLabels+1))
    (outside : ¬(base≤label.val ∧ label.val<base+(P.extraLabels+1))) :
    (installCodeBank P Q registers base fits).code label = Q.code label := by
  simp only [installCodeBank,dif_neg outside]

/-- The resulting concrete finite program contains the full reviewed bank. -/
def installedBankEmbedding (P Q : Program) (registers : BankRegisters P Q)
    (base : ℕ) (fits : base+(P.extraLabels+1)≤Q.extraLabels+1) :
    RoutineEmbedding P (installCodeBank P Q registers base fits) where
  labels := bankLabel P Q base fits
  reals := registers.reals
  naturals := registers.naturals
  constants := registers.constants
  reals_injective := registers.reals_injective
  naturals_injective := registers.naturals_injective
  constant_values := registers.constant_values
  code := by
    intro label hn
    have hmem : base≤(bankLabel P Q base fits label).val ∧
        (bankLabel P Q base fits label).val<base+(P.extraLabels+1) := by
      change base≤base+label.val ∧ base+label.val<base+(P.extraLabels+1)
      have := label.isLt
      omega
    unfold installCodeBank
    simp only [dif_pos hmem]
    have heq : (⟨(bankLabel P Q base fits label).val-base,by
        have := label.isLt
        simp only [bankLabel]
        omega⟩ : Fin (P.extraLabels+1)) = label := by
      apply Fin.ext
      simp only [bankLabel,Nat.add_sub_cancel_left]
    rw [heq,hn]
    rfl

/-- Installing a disjoint bank preserves every earlier literal embedding. -/
def RoutineEmbedding.throughInstalledBank {A P Q : Program}
    (E : RoutineEmbedding A Q) (registers : BankRegisters P Q)
    (base : ℕ) (fits : base+(P.extraLabels+1)≤Q.extraLabels+1)
    (outside : ∀ label,instructionIsHalt (A.code label)=false →
      ¬(base≤(E.labels label).val ∧ (E.labels label).val<base+(P.extraLabels+1))) :
    RoutineEmbedding A (installCodeBank P Q registers base fits) where
  labels := E.labels
  reals := E.reals
  naturals := E.naturals
  constants := E.constants
  reals_injective := E.reals_injective
  naturals_injective := E.naturals_injective
  constant_values := E.constant_values
  code := by
    intro label hn
    rw [installCodeBank_outside P Q registers base fits (E.labels label) (outside label hn)]
    exact E.code label hn

/-- A local halt cell retains the literal continuation supplied by the caller. -/
theorem installCodeBank_exit (P Q : Program) (registers : BankRegisters P Q)
    (base : ℕ) (fits : base+(P.extraLabels+1)≤Q.extraLabels+1)
    (label : Fin (P.extraLabels+1)) (halt : instructionIsHalt (P.code label)=true) :
    (installCodeBank P Q registers base fits).code (bankLabel P Q base fits label) =
      Q.code (bankLabel P Q base fits label) := by
  have hmem : base≤(bankLabel P Q base fits label).val ∧
      (bankLabel P Q base fits label).val<base+(P.extraLabels+1) := by
    change base≤base+label.val ∧ base+label.val<base+(P.extraLabels+1)
    have := label.isLt
    omega
  unfold installCodeBank
  simp only [dif_pos hmem]
  have heq : (⟨(bankLabel P Q base fits label).val-base,by
      have := label.isLt
      simp only [bankLabel]
      omega⟩ : Fin (P.extraLabels+1)) = label := by
    apply Fin.ext
    simp only [bankLabel,Nat.add_sub_cancel_left]
  rw [heq,halt]
  rfl

#assert_trust kernel BankRegisters
#assert_trust kernel offsetBankRegisters
#assert_trust kernel bankLabel
#assert_trust kernel installCodeBank
#assert_trust kernel installCodeBank_outside
#assert_trust kernel installedBankEmbedding
#assert_trust kernel RoutineEmbedding.throughInstalledBank
#assert_trust kernel installCodeBank_exit
#print axioms installedBankEmbedding
#print axioms RoutineEmbedding.throughInstalledBank
end NLA.Proofs.TR04
