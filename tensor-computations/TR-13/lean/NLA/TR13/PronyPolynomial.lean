import NLA.TR13.Prony

noncomputable section
open scoped BigOperators
open Polynomial Matrix

namespace NLA.TR13

section Ring
variable {R S : Type*} [CommRing R] [CommRing S]

def momentMatrix (r : ℕ) (h : ℕ → R) : Matrix (Fin r) (Fin r) R :=
  fun i j => h (i.val + j.val)

def shiftedMoments (r : ℕ) (h : ℕ → R) : Fin r → R :=
  fun i => h (i.val + r)

/-- Cramer's numerators are polynomial functions of the input moments. -/
def pronyCoefficients (r : ℕ) (h : ℕ → R) : Fin r → R :=
  Matrix.cramer (momentMatrix r h) (shiftedMoments r h)

def pronyPolynomial (r : ℕ) (h : ℕ → R) : R[X] := by
  classical
  exact C (momentMatrix r h).det * X ^ r - Polynomial.ofFn r (pronyCoefficients r h)

/-- A single polynomial condition ensures an invertible moment matrix and a
recurrence with distinct complex roots. Degrees in the resultant are fixed. -/
def pronyCertificate (r : ℕ) (h : ℕ → R) : R :=
  (momentMatrix r h).det *
    Polynomial.resultant (pronyPolynomial r h) (pronyPolynomial r h).derivative r (r - 1)

lemma momentMatrix_map (f : R →+* S) (r : ℕ) (h : ℕ → R) :
    f.mapMatrix (momentMatrix r h) = momentMatrix r (fun i => f (h i)) := rfl

lemma pronyCoefficients_map (f : R →+* S) (r : ℕ) (h : ℕ → R) (i : Fin r) :
    f (pronyCoefficients r h i) = pronyCoefficients r (fun j => f (h j)) i := by
  classical
  rw [pronyCoefficients, pronyCoefficients, Matrix.cramer_apply, Matrix.cramer_apply,
    f.map_det]
  congr 1
  ext j k
  simp [Matrix.map_apply, RingHom.mapMatrix_apply, Matrix.updateCol_apply,
    momentMatrix, shiftedMoments]
  split_ifs <;> rfl

lemma pronyPolynomial_map (f : R →+* S) (r : ℕ) (h : ℕ → R) :
    (pronyPolynomial r h).map f = pronyPolynomial r (fun i => f (h i)) := by
  classical
  simp only [pronyPolynomial, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum, Polynomial.map_monomial]
  rw [f.map_det, momentMatrix_map]
  congr 2
  funext i
  rw [pronyCoefficients_map]

lemma pronyCertificate_map (f : R →+* S) (r : ℕ) (h : ℕ → R) :
    f (pronyCertificate r h) = pronyCertificate r (fun i => f (h i)) := by
  unfold pronyCertificate
  rw [map_mul, f.map_det, momentMatrix_map, ← Polynomial.resultant_map_map]
  rw [← Polynomial.derivative_map, pronyPolynomial_map]

lemma prony_recurrence (r : ℕ) (h : ℕ → R) (i : Fin r) :
    (momentMatrix r h).det * h (i.val + r) =
      ∑ j, pronyCoefficients r h j * h (i.val + j.val) := by
  have hc := congrFun (Matrix.mulVec_cramer (momentMatrix r h) (shiftedMoments r h)) i
  simpa [momentMatrix, shiftedMoments, pronyCoefficients,
    Matrix.mulVec, dotProduct, mul_comm] using hc.symm

lemma pronyCertificate_congr {r : ℕ} {h k : ℕ → R}
    (hk : ∀ i < 2 * r, h i = k i) :
    pronyCertificate r h = pronyCertificate r k := by
  have hA : momentMatrix r h = momentMatrix r k := by
    ext i j
    exact hk _ (by omega)
  have hb : shiftedMoments r h = shiftedMoments r k := by
    ext i
    exact hk _ (by omega)
  have hp : pronyPolynomial r h = pronyPolynomial r k := by
    unfold pronyPolynomial pronyCoefficients
    rw [hA, hb]
  unfold pronyCertificate
  rw [hA, hp]

end Ring

lemma pronyPolynomial_eq_recurrencePolynomial (r : ℕ) (h : ℕ → ℂ) :
    pronyPolynomial r h = recurrencePolynomial r (momentMatrix r h).det
      (pronyCoefficients r h) := rfl

lemma pronyPolynomial_natDegree {r : ℕ} (hr : 0 < r) (h : ℕ → ℂ)
    (hdet : (momentMatrix r h).det ≠ 0) : (pronyPolynomial r h).natDegree = r :=
  recurrencePolynomial_natDegree hr hdet _

lemma pronyPolynomial_separable {r : ℕ} (hr : 0 < r) (h : ℕ → ℂ)
    (hcert : pronyCertificate r h ≠ 0) : (pronyPolynomial r h).Separable := by
  have hdet : (momentMatrix r h).det ≠ 0 := (mul_ne_zero_iff.mp hcert).1
  have hres := (mul_ne_zero_iff.mp hcert).2
  have hdeg := pronyPolynomial_natDegree hr h hdet
  have hp : pronyPolynomial r h ≠ 0 := by
    intro hz
    simp [hz] at hdeg
    omega
  change IsCoprime (pronyPolynomial r h) (pronyPolynomial r h).derivative
  by_contra hbad
  apply hres
  have heq := Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hp, hbad⟩
  simpa [hdeg, Polynomial.natDegree_derivative] using heq

/-- The polynomial certificate yields an actual finite-node moment representation. -/
theorem pronyCertificate_representation {r : ℕ} (hr : 0 < r) (h : ℕ → ℂ)
    (hcert : pronyCertificate r h ≠ 0) :
    ∃ c t : Fin r → ℂ, ∀ i < 2 * r, h i = ∑ j, c j * t j ^ i := by
  apply prony_representation hr h ((mul_ne_zero_iff.mp hcert).1) (pronyCoefficients r h)
  · exact prony_recurrence r h
  · exact pronyPolynomial_separable hr h hcert

end NLA.TR13
