/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.Definitions
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.TR06
variable {d : ℕ} {n : Fin d → ℕ}

/-- Coordinatewise scalar extension; the original real tensor is recoverable. -/
def complexify (A : Tensor ℝ d n) : Tensor ℂ d n :=
  WithLp.toLp 2 (fun q => (A q : ℂ))

@[simp] theorem complexify_apply (A : Tensor ℝ d n) (q : TensorIndex d n) :
    complexify A q = (A q : ℂ) := rfl

theorem complexify_injective : Function.Injective (complexify (d := d) (n := n)) := by
  intro A B h
  ext q
  exact Complex.ofReal_injective (congrArg (fun x : Tensor ℂ d n => x q) h)

@[simp] theorem complexify_zero : complexify (0 : Tensor ℝ d n) = 0 := by
  ext q
  simp [complexify]

@[simp] theorem complexify_add (A B : Tensor ℝ d n) :
    complexify (A + B) = complexify A + complexify B := by
  ext q
  simp [complexify]

@[simp] theorem complexify_sum {ι : Type*} (s : Finset ι) (a : ι → Tensor ℝ d n) :
    complexify (∑ i ∈ s, a i) = ∑ i ∈ s, complexify (a i) := by
  ext q
  simp [complexify]

@[simp] theorem complexify_pureTensor (u : (j : Fin d) → Fin (n j) → ℝ) :
    complexify (pureTensor u) = pureTensor (fun j i => (u j i : ℂ)) := by
  ext q
  simp [complexify, pureTensor]

theorem complexify_rankOne {A : Tensor ℝ d n} (hA : RankOne A) :
    RankOne (complexify A) := by
  constructor
  · intro hzero
    apply hA.1
    apply complexify_injective
    simpa only [complexify_zero] using hzero
  · obtain ⟨u, hu⟩ := hA.2
    exact ⟨fun j i => (u j i : ℂ), by rw [← complexify_pureTensor, hu]⟩

theorem complexify_decomposes {r : ℕ} {a : Fin r → Tensor ℝ d n} {A : Tensor ℝ d n}
    (ha : Decomposes a A) : Decomposes (fun i => complexify (a i)) (complexify A) := by
  refine ⟨fun i => complexify_rankOne (ha.1 i), ?_⟩
  rw [← complexify_sum, ha.2]

/-- Real exactness follows when a real decomposition exists and its
complexification has the same exact rank. This asserts no universal rank equality. -/
theorem exactRank_of_complexify {r : ℕ} {A : Tensor ℝ d n}
    (hreal : ∃ a : Fin r → Tensor ℝ d n, Decomposes a A)
    (hcomplex : ExactRank r (complexify A)) : ExactRank r A := by
  refine ⟨hreal, ?_⟩
  intro m hm ⟨a, ha⟩
  exact hcomplex.2 m hm ⟨fun i => complexify (a i), complexify_decomposes ha⟩

theorem identifiable_of_complexify {r : ℕ} {A : Tensor ℝ d n}
    (hcomplex : Identifiable r (complexify A)) : Identifiable r A := by
  intro a b ha hb
  obtain ⟨σ, hσ⟩ := hcomplex (fun i => complexify (a i))
    (fun i => complexify (b i)) (complexify_decomposes ha) (complexify_decomposes hb)
  exact ⟨σ, fun i => complexify_injective (hσ i)⟩

theorem exact_identifiable_of_complexify {r : ℕ} {A : Tensor ℝ d n}
    (hreal : ∃ a : Fin r → Tensor ℝ d n, Decomposes a A)
    (hcomplex : ExactRank r (complexify A) ∧ Identifiable r (complexify A)) :
    ExactRank r A ∧ Identifiable r A :=
  ⟨exactRank_of_complexify hreal hcomplex.1, identifiable_of_complexify hcomplex.2⟩

#print axioms complexify_decomposes
#print axioms exact_identifiable_of_complexify
#assert_trust kernel complexify_decomposes
#assert_trust kernel exact_identifiable_of_complexify
end NLA.TR06
