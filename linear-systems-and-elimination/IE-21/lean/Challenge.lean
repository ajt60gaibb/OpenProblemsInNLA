import Definitions

set_option autoImplicit false

namespace IE21

/- Full approved target.  The declaration is intentionally a Challenge
   specification; it is not imported by Solution.  `SphericalRowLaw` is the
   sole infrastructure boundary recorded in the blocker report. -/
axiom full_result
    (theta : ℝ) (hθ : 0 < theta ∧ theta < 1)
    (a h : ℝ) (ha : GaussianQuantile theta a) (hh : h = gaussianH theta a)
    (D : SequenceData) :
    ProbLimit D (fun j A => (D.n j : ℝ) / D.m j * sThetaSq theta A) h ∧
    ProbLimit D (fun j A => (D.n j : ℝ) / D.m j * opNormSq A) 1 ∧
    ProbLimit D (ratioValue theta D) h

theorem l2Sq_zero (n : ℕ) : l2Sq (fun _ : Fin n => (0 : ℝ)) = 0 := by
  simp [l2Sq]

theorem rowEnergy_empty {m n : ℕ} (A : Matrix m n) (x : Fin n → ℝ) :
    rowEnergy A ∅ x = 0 := by
  simp [rowEnergy]

#print axioms full_result

end IE21
