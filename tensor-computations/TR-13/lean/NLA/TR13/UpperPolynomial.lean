import NLA.TR13.PronyWitness
import Mathlib.Algebra.MvPolynomial.Funext

noncomputable section
open scoped BigOperators
open Polynomial Matrix

namespace NLA.TR13

/-- Universal finite moments, extended by zero. Only the final required Prony
moment can lie outside the input vector. -/
def momentVariables (D i : ℕ) : MvPolynomial (Fin (D + 1)) ℂ :=
  if hi : i < D + 1 then MvPolynomial.X ⟨i, hi⟩ else 0

def upperPolynomial (D r : ℕ) : MvPolynomial (Fin (D + 1)) ℂ :=
  pronyCertificate r (momentVariables D)

def extendMoments {D : ℕ} (h : Fin (D + 1) → ℂ) (i : ℕ) : ℂ :=
  if hi : i < D + 1 then h ⟨i, hi⟩ else 0

lemma eval_momentVariables {D : ℕ} (h : Fin (D + 1) → ℂ) (i : ℕ) :
    MvPolynomial.eval h (momentVariables D i) = extendMoments h i := by
  unfold momentVariables extendMoments
  split_ifs <;> simp

lemma eval_upperPolynomial {D r : ℕ} (h : Fin (D + 1) → ℂ) :
    MvPolynomial.eval h (upperPolynomial D r) =
      pronyCertificate r (extendMoments h) := by
  unfold upperPolynomial
  rw [pronyCertificate_map]
  simp_rw [eval_momentVariables]

lemma periodicMoment_last_zero {r : ℕ} (hr : 2 ≤ r) :
    periodicMoment r (2 * r - 1) = 0 := by
  have he : 2 * r - 1 = (r - 1) + r := by omega
  rw [he, periodicMoment_add]
  simp [periodicMoment, Nat.mod_eq_of_lt (show r - 1 < r by omega),
    show r - 1 ≠ 0 by omega]

lemma extend_periodicMoment {D r : ℕ} (hr : 2 ≤ r) (hD : 2 * r ≤ D + 2)
    (i : ℕ) (hi : i < 2 * r) :
    extendMoments (fun j : Fin (D + 1) => periodicMoment r j.val) i =
      periodicMoment r i := by
  unfold extendMoments
  split_ifs with hib
  · rfl
  · have he : i = 2 * r - 1 := by omega
    rw [he, periodicMoment_last_zero hr]

/-- The certificate is a nonzero multivariate polynomial, including when the
last moment is fixed to zero in the odd-dimensional moment space. -/
theorem upperPolynomial_ne_zero {D r : ℕ} (hr : 2 ≤ r) (hD : 2 * r ≤ D + 2) :
    upperPolynomial D r ≠ 0 := by
  intro hz
  have he := congrArg (MvPolynomial.eval
    (fun j : Fin (D + 1) => periodicMoment r j.val)) hz
  rw [eval_upperPolynomial, map_zero] at he
  have hc : pronyCertificate r
      (extendMoments (fun j : Fin (D + 1) => periodicMoment r j.val)) =
      pronyCertificate r (periodicMoment r) :=
    pronyCertificate_congr (extend_periodicMoment hr hD)
  rw [hc] at he
  exact periodicMoment_certificate_ne_zero (by omega) he

theorem generic_moment_representation {D r : ℕ} (hr : 2 ≤ r)
    (hlo : 2 * r ≤ D + 2) (hhi : D < 2 * r) :
    upperPolynomial D r ≠ 0 ∧
      ∀ h : Fin (D + 1) → ℂ, MvPolynomial.eval h (upperPolynomial D r) ≠ 0 →
        ∃ c t : Fin r → ℂ, ∀ i : Fin (D + 1), h i = ∑ j, c j * t j ^ i.val := by
  refine ⟨upperPolynomial_ne_zero hr hlo, ?_⟩
  intro h hp
  rw [eval_upperPolynomial] at hp
  obtain ⟨c, t, hct⟩ := pronyCertificate_representation (by omega) (extendMoments h) hp
  refine ⟨c, t, ?_⟩
  intro i
  simpa [extendMoments, i.isLt] using hct i.val (by omega)

end NLA.TR13
