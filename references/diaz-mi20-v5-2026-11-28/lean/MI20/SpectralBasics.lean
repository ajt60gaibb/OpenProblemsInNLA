/-
  MI20/SpectralBasics.lean
  ========================
  Author: Marcio Díaz (Space Research AI, https://spaceresearch.ai, marcio.diaz@gmail.com)
  SVD (`exists_svd`), unitary polar decomposition (`exists_polar_unitary`), and Schatten basics.
-/

import MI20.Definitions
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section

namespace MI20

/-! ### Basic properties of `matAbs` and Hermitian/PSD matrices -/

lemma matAbs_posSemidef {n : ℕ} (A : Mat n) : (matAbs A).PosSemidef := by
  rw [matAbs, ← Matrix.nonneg_iff_posSemidef]
  exact CFC.sqrt_nonneg _

lemma matAbs_isHermitian {n : ℕ} (A : Mat n) : (matAbs A).IsHermitian :=
  (matAbs_posSemidef A).isHermitian

lemma matAbs_mul_self {n : ℕ} (A : Mat n) : matAbs A * matAbs A = Aᴴ * A := by
  rw [matAbs]
  exact CFC.sqrt_mul_sqrt_self (Aᴴ * A)
    (Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self A))

lemma matAbs_eq_of_posSemidef_sq {n : ℕ} {A P : Mat n}
    (hP : P.PosSemidef) (hsq : P * P = Aᴴ * A) : matAbs A = P := by
  rw [matAbs, ← hsq]
  exact CFC.sqrt_mul_self P (Matrix.nonneg_iff_posSemidef.mpr hP)

lemma matAbs_of_posSemidef {n : ℕ} {P : Mat n} (hP : P.PosSemidef) : matAbs P = P :=
  matAbs_eq_of_posSemidef_sq hP (by rw [hP.isHermitian.eq])

lemma matAbs_zero {n : ℕ} : matAbs (0 : Mat n) = 0 :=
  matAbs_of_posSemidef Matrix.PosSemidef.zero

lemma unitary_conjTranspose_mul_self {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (U : Mat n)ᴴ * (U : Mat n) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp U.2

lemma unitary_mul_conjTranspose_self {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (U : Mat n) * (U : Mat n)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp U.2

lemma matAbs_unitary_mul {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (A : Mat n) :
    matAbs ((U : Mat n) * A) = matAbs A := by
  apply matAbs_eq_of_posSemidef_sq (matAbs_posSemidef A)
  rw [matAbs_mul_self, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n) A, unitary_conjTranspose_mul_self U, Matrix.one_mul]

lemma matAbs_isometry_mul {m n : ℕ} (R : Matrix (Fin m) (Fin n) ℂ)
    (hR : Rᴴ * R = 1) (A : Mat n) :
    CFC.sqrt ((R * A)ᴴ * (R * A)) = matAbs A := by
  have h : (R * A)ᴴ * (R * A) = Aᴴ * A := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ R A, hR, Matrix.one_mul]
  rw [h, matAbs]

lemma matAbs_eq_rpow_half {n : ℕ} (A : Mat n) :
    matAbs A = CFC.rpow (Aᴴ * A) (1 / 2 : ℝ) := by
  rw [matAbs, CFC.sqrt_eq_rpow]
  rfl

lemma toEuclideanLin_gram {n : ℕ} (A : Mat n) :
    Matrix.toEuclideanLin (Aᴴ * A) =
      (Matrix.toEuclideanLin A).adjoint ∘ₗ Matrix.toEuclideanLin A := by
  rw [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

/-! ### Eigenvalue / singular value and CFC trace bridges -/

lemma singularValue_eq_sqrt_eigenvalue₀ {n : ℕ} (A : Mat n) (i : Fin n) :
    singularValue A i =
      Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀
        (i.cast (Fintype.card_fin n).symm)) := by
  have h := (Matrix.toEuclideanLin A).singularValues_fin finrank_euclideanSpace
    (i.cast (Fintype.card_fin n).symm)
  simpa only [singularValue, Fin.val_cast, Matrix.IsHermitian.eigenvalues₀, toEuclideanLin_gram]
    using h

lemma schattenPow_eq_sum_gram_eigenvalues {n : ℕ} (p : ℝ) (A : Mat n) :
    schattenPow p A =
      ∑ i : Fin n,
        (Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i)) ^ p := by
  rw [schattenPow]
  let hG := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _)
  calc ∑ i : Fin n, (singularValue A i) ^ p
      = ∑ i : Fin n, (Real.sqrt (hG.eigenvalues₀ (i.cast (Fintype.card_fin n).symm))) ^ p := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [singularValue_eq_sqrt_eigenvalue₀]
    _ = ∑ j : Fin (Fintype.card (Fin n)), (Real.sqrt (hG.eigenvalues₀ j)) ^ p := by
          refine Fintype.sum_equiv (finCongr (Fintype.card_fin n).symm) _ _ fun _ => rfl
    _ = ∑ i : Fin n, (Real.sqrt (hG.eigenvalues i)) ^ p := by
          refine Fintype.sum_equiv e _ _ fun j => ?_
          simp [Matrix.IsHermitian.eigenvalues, e]

lemma schattenPow_eq_sum_gram_rpow {n : ℕ} (p : ℝ) (A : Mat n) :
    schattenPow p A =
      ∑ i : Fin n,
        ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i) ^ (p / 2) := by
  rw [schattenPow_eq_sum_gram_eigenvalues]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hnn : 0 ≤ (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i :=
    (Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg i
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnn]
  ring_nf

lemma trace_hermitian_cfc {n : ℕ} {A : Mat n} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (hA.cfc f).trace = ∑ i : Fin n, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle,
    show star (hA.eigenvectorUnitary : Mat n) = (hA.eigenvectorUnitary : Mat n)ᴴ from rfl,
    unitary_conjTranspose_mul_self hA.eigenvectorUnitary, Matrix.one_mul, Matrix.trace_diagonal]
  rfl

lemma trace_cfc_re {n : ℕ} {A : Mat n} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace.re = ∑ i : Fin n, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq, trace_hermitian_cfc, Complex.re_sum]
  simp

lemma schattenPow_eq_trace_cfc {n : ℕ} (p : ℝ) (A : Mat n) :
    schattenPow p A = (cfc (fun x : ℝ => x ^ (p / 2)) (Aᴴ * A)).trace.re := by
  rw [schattenPow_eq_sum_gram_rpow,
    trace_cfc_re (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian]

lemma schattenPow_nonneg {n : ℕ} (p : ℝ) (A : Mat n) : 0 ≤ schattenPow p A :=
  Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ((Matrix.toEuclideanLin A).singularValues_nonneg _) p

lemma schattenNorm_nonneg {n : ℕ} (p : ℝ) (A : Mat n) : 0 ≤ schattenNorm p A :=
  Real.rpow_nonneg (schattenPow_nonneg p A) _

lemma schattenPow_zero {n : ℕ} {p : ℝ} (hp : 0 < p) : schattenPow p (0 : Mat n) = 0 := by
  simp [schattenPow, singularValue, LinearMap.singularValues_zero, Real.zero_rpow hp.ne']

lemma schattenPow_pos_iff {n : ℕ} {p : ℝ} (hp : 0 < p) (A : Mat n) :
    0 < schattenPow p A ↔ A ≠ 0 := by
  constructor
  · intro hpos hA
    subst hA
    rw [schattenPow_zero hp] at hpos
    exact lt_irrefl 0 hpos
  · intro hA
    have hT : Matrix.toEuclideanLin A ≠ 0 := by
      intro h
      exact hA (Matrix.toEuclideanLin.injective (by simpa using h))
    have hsv : (Matrix.toEuclideanLin A).singularValues ≠ 0 :=
      mt (LinearMap.singularValues_eq_zero_iff (T := Matrix.toEuclideanLin A)).mp hT
    have h0 : 0 < singularValue A 0 := by
      by_contra hle
      push Not at hle
      have hzero : singularValue A 0 = 0 :=
        le_antisymm hle ((Matrix.toEuclideanLin A).singularValues_nonneg 0)
      apply hsv
      ext k
      have hanti := (Matrix.toEuclideanLin A).singularValues_antitone (Nat.zero_le k)
      have hnn := (Matrix.toEuclideanLin A).singularValues_nonneg k
      exact le_antisymm (hanti.trans hzero.le) hnn
    have hn : 0 < n := by
      by_contra hn0
      have hn' : n = 0 := Nat.eq_zero_of_not_pos hn0
      subst hn'
      exact hA (Subsingleton.elim _ _)
    refine Finset.sum_pos' (fun _ _ => Real.rpow_nonneg
      ((Matrix.toEuclideanLin A).singularValues_nonneg _) p) ⟨⟨0, hn⟩, Finset.mem_univ _, ?_⟩
    exact Real.rpow_pos_of_pos h0 p

lemma schattenNorm_pos_iff {n : ℕ} {p : ℝ} (hp : 0 < p) (A : Mat n) :
    0 < schattenNorm p A ↔ A ≠ 0 := by
  rw [schattenNorm, ← schattenPow_pos_iff hp A]
  constructor
  · intro h
    by_contra hle
    have h0 : schattenPow p A = 0 := le_antisymm (not_lt.mp hle) (schattenPow_nonneg p A)
    rw [h0, Real.zero_rpow (one_div_pos.mpr hp).ne'] at h
    exact lt_irrefl 0 h
  · intro h
    exact Real.rpow_pos_of_pos h (1 / p)

lemma schattenPow_eq_of_gram_eq {n : ℕ} (p : ℝ) {A B : Mat n} (h : Aᴴ * A = Bᴴ * B) :
    schattenPow p A = schattenPow p B := by
  rw [schattenPow_eq_trace_cfc, schattenPow_eq_trace_cfc, h]

lemma schattenPow_matAbs {n : ℕ} (p : ℝ) (A : Mat n) :
    schattenPow p (matAbs A) = schattenPow p A := by
  apply schattenPow_eq_of_gram_eq
  rw [(matAbs_isHermitian A).eq, matAbs_mul_self]

lemma schattenNorm_matAbs {n : ℕ} (p : ℝ) (A : Mat n) :
    schattenNorm p (matAbs A) = schattenNorm p A := by
  simp only [schattenNorm, schattenPow_matAbs]

lemma spectrum_real_nonneg_of_posSemidef {n : ℕ} {P : Mat n} (hP : P.PosSemidef) :
    ∀ x ∈ spectrum ℝ P, 0 ≤ x :=
  spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hP)

lemma schattenPow_posSemidef {n : ℕ} {p : ℝ} (hp : 0 < p) {P : Mat n} (hP : P.PosSemidef) :
    schattenPow p P = ∑ i : Fin n, (hP.isHermitian.eigenvalues i) ^ p := by
  rw [schattenPow_eq_trace_cfc]
  have hP2 : Pᴴ * P = cfc (fun x : ℝ => x ^ (2 : ℕ)) P := by
    rw [hP.isHermitian.eq, cfc_pow_id (R := ℝ) P 2, sq]
  have hsa : IsSelfAdjoint P := hP.isHermitian.isSelfAdjoint
  have hspec_nn : ∀ x ∈ spectrum ℝ P, 0 ≤ x := spectrum_real_nonneg_of_posSemidef hP
  have hcont1 : ContinuousOn (fun x : ℝ => x ^ (2 : ℕ)) (spectrum ℝ P) :=
    (continuous_pow 2).continuousOn
  have hcont2 : ContinuousOn (fun x : ℝ => x ^ (p / 2)) ((fun x : ℝ => x ^ (2 : ℕ)) '' spectrum ℝ P) :=
    (Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ p / 2)).continuousOn
  rw [hP2, ← cfc_comp (fun x : ℝ => x ^ (p / 2)) (fun x : ℝ => x ^ (2 : ℕ)) P hsa hcont2 hcont1]
  have hcongr : cfc ((fun x : ℝ => x ^ (p / 2)) ∘ (fun x : ℝ => x ^ (2 : ℕ))) P =
      cfc (fun x : ℝ => x ^ p) P := by
    apply cfc_congr
    intro x hx
    simp only [Function.comp_apply]
    have hx0 : 0 ≤ x := hspec_nn x hx
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx0]
    have h2 : (2 : ℝ) * (p / 2) = p := by ring
    exact congrArg (x ^ ·) (by exact_mod_cast h2)
  rw [hcongr, trace_cfc_re hP.isHermitian]

lemma schattenPow_eq_trace_cfc_posSemidef {n : ℕ} {p : ℝ} (hp : 0 < p)
    {P : Mat n} (hP : P.PosSemidef) :
    schattenPow p P = (cfc (fun x : ℝ => x ^ p) P).trace.re := by
  rw [schattenPow_posSemidef hp hP, trace_cfc_re hP.isHermitian]

/-! ### Unitary invariance, diagonal formula, and scaling -/

lemma cfc_conj_unitary {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) {A : Mat n}
    (hA : A.IsHermitian) {f : ℝ → ℝ} (hf : ContinuousOn f (spectrum ℝ A)) :
    cfc f ((U : Mat n) * A * (U : Mat n)ᴴ) = (U : Mat n) * cfc f A * (U : Mat n)ᴴ := by
  have hcont : Continuous (fun X : Mat n => ((Unitary.conjStarAlgAut ℂ (Mat n) U) X)) := by
    have hfun : (fun X : Mat n => ((Unitary.conjStarAlgAut ℂ (Mat n) U) X)) =
        (fun X : Mat n => (U : Mat n) * X * (U : Mat n)ᴴ) := by
      ext X i j; rfl
    rw [hfun]
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hA' : IsSelfAdjoint (((Unitary.conjStarAlgAut ℂ (Mat n) U) A)) :=
    IsSelfAdjoint.map hA.isSelfAdjoint (Unitary.conjStarAlgAut ℂ (Mat n) U).toStarAlgHom
  have h := StarAlgHom.map_cfc (Unitary.conjStarAlgAut ℂ (Mat n) U).toStarAlgHom f A hf hcont hA.isSelfAdjoint hA'
  simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using h.symm

lemma schattenPow_unitary_mul_left {n : ℕ} (p : ℝ) (U : Matrix.unitaryGroup (Fin n) ℂ) (A : Mat n) :
    schattenPow p ((U : Mat n) * A) = schattenPow p A := by
  apply schattenPow_eq_of_gram_eq
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n) A,
    unitary_conjTranspose_mul_self U, Matrix.one_mul]

lemma schattenPow_unitary_mul_right {n : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (A : Mat n) (V : Matrix.unitaryGroup (Fin n) ℂ) :
    schattenPow p (A * (V : Mat n)) = schattenPow p A := by
  rw [schattenPow_eq_trace_cfc, schattenPow_eq_trace_cfc]
  have hG : (A * (V : Mat n))ᴴ * (A * (V : Mat n)) = (V : Mat n)ᴴ * (Aᴴ * A) * (V : Mat n) := by
    rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [hG]
  let Vstar : Matrix.unitaryGroup (Fin n) ℂ := star V
  have hconj : (V : Mat n)ᴴ * (Aᴴ * A) * (V : Mat n) =
      (Vstar : Mat n) * (Aᴴ * A) * (Vstar : Mat n)ᴴ := by
    change (V : Mat n)ᴴ * (Aᴴ * A) * (V : Mat n) = (V : Mat n)ᴴ * (Aᴴ * A) * (V : Mat n)ᴴᴴ
    rw [Matrix.conjTranspose_conjTranspose]
  have hcont : ContinuousOn (fun x : ℝ => x ^ (p / 2)) (spectrum ℝ (Aᴴ * A)) :=
    (Real.continuous_rpow_const (by linarith)).continuousOn
  rw [hconj, cfc_conj_unitary Vstar (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian hcont]
  rw [Matrix.trace_mul_cycle, unitary_conjTranspose_mul_self Vstar, Matrix.one_mul]

lemma schattenPow_smul {n : ℕ} {p : ℝ} (hp : 0 < p) (c : ℂ) (A : Mat n) :
    schattenPow p (c • A) = ‖c‖ ^ p * schattenPow p A := by
  by_cases hc : c = 0
  · subst hc
    simp [schattenPow_zero hp, Real.zero_rpow hp.ne']
  · rw [schattenPow_eq_trace_cfc, schattenPow_eq_trace_cfc]
    have hsm : (c • A)ᴴ * (c • A) = (‖c‖ ^ (2 : ℕ) : ℝ) • (Aᴴ * A) := by
      have h1 : (c • A)ᴴ * (c • A) = ((‖c‖ ^ (2 : ℕ) : ℝ) : ℂ) • (Aᴴ * A) := by
        rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          show star c * c = ((‖c‖ ^ (2 : ℕ) : ℝ) : ℂ) by
            rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]]
      rw [h1]; rfl
    have hG := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
    have hcont_rpow : ContinuousOn (fun x : ℝ => x ^ (p / 2)) (spectrum ℝ (Aᴴ * A)) :=
      (Real.continuous_rpow_const (by linarith)).continuousOn
    have hcont_rpow2 : ContinuousOn (fun x : ℝ => x ^ (p / 2))
        ((fun x : ℝ => (‖c‖ ^ (2 : ℕ)) * x) '' spectrum ℝ (Aᴴ * A)) :=
      (Real.continuous_rpow_const (by linarith)).continuousOn
    have hcfc_sm : cfc (fun x : ℝ => x ^ (p / 2)) ((‖c‖ ^ (2 : ℕ) : ℝ) • (Aᴴ * A)) =
        (‖c‖ ^ p : ℝ) • cfc (fun x : ℝ => x ^ (p / 2)) (Aᴴ * A) := by
      have h1 : (‖c‖ ^ (2 : ℕ) : ℝ) • (Aᴴ * A) = cfc (fun x : ℝ => (‖c‖ ^ (2 : ℕ)) * x) (Aᴴ * A) := by
        rw [cfc_const_mul_id (R := ℝ) (‖c‖ ^ (2 : ℕ)) (Aᴴ * A)]
      rw [h1, ← cfc_comp (fun x : ℝ => x ^ (p / 2)) (fun x : ℝ => (‖c‖ ^ (2 : ℕ)) * x) (Aᴴ * A)
        hG.isSelfAdjoint hcont_rpow2 (continuous_const.mul continuous_id).continuousOn]
      have hcongr : cfc ((fun x : ℝ => x ^ (p / 2)) ∘ (fun x : ℝ => (‖c‖ ^ (2 : ℕ)) * x)) (Aᴴ * A) =
          cfc (fun x : ℝ => ‖c‖ ^ p * (x ^ (p / 2))) (Aᴴ * A) := by
        apply cfc_congr
        intro x hx
        have hx0 : 0 ≤ x :=
          spectrum_real_nonneg_of_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A) x hx
        simp only [Function.comp_apply]
        rw [Real.mul_rpow (sq_nonneg ‖c‖) hx0, ← Real.rpow_natCast ‖c‖ 2,
          ← Real.rpow_mul (norm_nonneg c)]
        have h2 : (2 : ℝ) * (p / 2) = p := by ring
        rw [show ((2 : ℕ) : ℝ) * (p / 2) = p by exact_mod_cast h2]
      rw [hcongr, cfc_const_mul (R := ℝ) (‖c‖ ^ p) (fun x : ℝ => x ^ (p / 2)) (Aᴴ * A) hcont_rpow]
    rw [hsm, hcfc_sm]
    simp [Matrix.trace_smul]

lemma cfc_diagonal_real {n : ℕ} (d : Fin n → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  let D : Mat n := Matrix.diagonal (fun i => (d i : ℂ))
  have hD : D.IsHermitian := by
    ext i j; by_cases h : i = j
    · subst h; simp [D]
    · simp [D, Matrix.diagonal, h, Ne.symm h]
  rw [hD.cfc_eq]
  -- Check action on every standard basis vector e_j using eigenbasis expansion
  let b := hD.eigenvectorBasis
  have hmul : ∀ j : Fin n, (hD.cfc f).mulVec (Pi.single j 1) = ((f (d j) : ℝ) : ℂ) • Pi.single j 1 := by
    intro j
    let ej : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (Pi.single j 1)
    have hDej : Matrix.toEuclideanLin D ej = (d j : ℂ) • ej := by
      apply WithLp.ofLp_injective
      ext i
      change (D.mulVec (Pi.single j (1 : ℂ))) i = (d j : ℂ) * (Pi.single j (1 : ℂ) : Fin n → ℂ) i
      rw [Matrix.mulVec_diagonal]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have hcoeff : ∀ k : Fin n, inner ℂ (b k) ej ≠ 0 → hD.eigenvalues k = d j := by
      intro k hk
      have h1 : inner ℂ (b k) (Matrix.toEuclideanLin D ej) = (d j : ℂ) * inner ℂ (b k) ej := by
        rw [hDej, inner_smul_right]
      have h2 : inner ℂ (b k) (Matrix.toEuclideanLin D ej) =
          (hD.eigenvalues k : ℂ) * inner ℂ (b k) ej := by
        have hadj : (Matrix.toEuclideanLin D).adjoint = Matrix.toEuclideanLin D := by
          rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hD.eq]
        rw [← LinearMap.adjoint_inner_left, hadj]
        have heig : Matrix.toEuclideanLin D (b k) = (hD.eigenvalues k : ℂ) • (b k) := by
          apply WithLp.ofLp_injective
          simpa [Matrix.toLpLin_apply, Matrix.toEuclideanLin, b] using hD.mulVec_eigenvectorBasis k
        rw [heig, inner_smul_left, Complex.conj_ofReal]
      have h3 : ((hD.eigenvalues k : ℂ) - (d j : ℂ)) * inner ℂ (b k) ej = 0 := by
        linear_combination h1 - h2
      have h4 : (hD.eigenvalues k : ℂ) = (d j : ℂ) := sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hk)
      exact Complex.ofReal_injective h4
    have hcfc_b : ∀ k : Fin n,
        Matrix.toEuclideanLin (hD.cfc f) (b k) = ((f (hD.eigenvalues k) : ℝ) : ℂ) • (b k) := by
      intro k
      apply WithLp.ofLp_injective
      ext i
      change ((hD.cfc f).mulVec (b k).ofLp) i = ((f (hD.eigenvalues k) : ℝ) : ℂ) * (b k).ofLp i
      rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
      have hUcol : ∀ a c, (hD.eigenvectorUnitary : Mat n) a c = (b c).ofLp a := fun a c => by
        simp [b, Matrix.IsHermitian.eigenvectorUnitary_apply]
      have hUH_b : (hD.eigenvectorUnitary : Mat n)ᴴ.mulVec (b k).ofLp = Pi.single k 1 := by
        ext r
        simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, hUcol, Pi.single_apply]
        have hin := orthonormal_iff_ite.mp b.orthonormal r k
        rw [EuclideanSpace.inner_eq_star_dotProduct] at hin
        simpa [dotProduct, mul_comm, eq_comm] using hin
      rw [show star (hD.eigenvectorUnitary : Mat n) = (hD.eigenvectorUnitary : Mat n)ᴴ from rfl,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hUH_b]
      simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply, b, mul_comm]
    have hLin : Matrix.toEuclideanLin (hD.cfc f) ej = ((f (d j) : ℝ) : ℂ) • ej := by
      conv_lhs => rw [← b.sum_repr' ej]
      rw [map_sum]
      conv_rhs => rw [← b.sum_repr' ej, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hcfc_b k, smul_comm]
      by_cases hk : inner ℂ (b k) ej = 0
      · simp [hk]
      · rw [hcoeff k hk]
    exact congrArg WithLp.ofLp hLin
  ext i j
  have h1 := congr_fun (hmul j) i
  by_cases hij : i = j
  · subst hij; simpa [Matrix.mulVec_single, Matrix.diagonal] using h1
  · simpa [Matrix.mulVec_single, Matrix.diagonal, Pi.single_apply, hij] using h1

lemma schattenPow_diagonal {n : ℕ} {p : ℝ} (hp : 0 < p) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    schattenPow p (Matrix.diagonal (fun i => (d i : ℂ))) = ∑ i : Fin n, (d i) ^ p := by
  have hP : (Matrix.diagonal (fun i => (d i : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i; exact_mod_cast hd i
  rw [schattenPow_eq_trace_cfc_posSemidef hp hP, cfc_diagonal_real, Matrix.trace_diagonal, Complex.re_sum]
  simp

/-! ### Singular Value Decomposition (SVD) and Polar Decomposition -/

/-- Every n × n complex matrix admits an SVD A = U * diag(σ) * Vᴴ with unitary U, V and σ ≥ 0. -/
theorem exists_svd {n : ℕ} (A : Mat n) :
    ∃ (U V : Matrix.unitaryGroup (Fin n) ℂ) (σ : Fin n → ℝ),
      (∀ i, 0 ≤ σ i) ∧
      A = (U : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (V : Mat n)ᴴ ∧
      (∀ p : ℝ, 0 < p → schattenPow p A = ∑ i : Fin n, (σ i) ^ p) := by
  let hG := Matrix.posSemidef_conjTranspose_mul_self A
  let V : Matrix.unitaryGroup (Fin n) ℂ := hG.isHermitian.eigenvectorUnitary
  let lam : Fin n → ℝ := hG.isHermitian.eigenvalues
  let σ : Fin n → ℝ := fun i => Real.sqrt (lam i)
  have hσ_nn : ∀ i, 0 ≤ σ i := fun i => Real.sqrt_nonneg _
  let bV : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) := hG.isHermitian.eigenvectorBasis
  let S : Finset (Fin n) := Finset.univ.filter (fun i => σ i ≠ 0)
  let Scomp : Finset (Fin n) := Finset.univ.filter (fun i => σ i = 0)
  let w : S → EuclideanSpace ℂ (Fin n) := fun i =>
    (((σ i.1)⁻¹ : ℝ) : ℂ) • (Matrix.toEuclideanLin A (bV i.1))
  have hbV_eig : ∀ j : Fin n, Matrix.toEuclideanLin (Aᴴ * A) (bV j) = (lam j : ℂ) • (bV j) := by
    intro j
    apply WithLp.ofLp_injective
    simpa [Matrix.toLpLin_apply, Matrix.toEuclideanLin, bV, lam] using hG.isHermitian.mulVec_eigenvectorBasis j
  have hw_orth : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi_ne : σ i.1 ≠ 0 := (Finset.mem_filter.mp i.2).2
    have hinner : inner ℂ (Matrix.toEuclideanLin A (bV i.1)) (Matrix.toEuclideanLin A (bV j.1)) =
        inner ℂ (bV i.1) (Matrix.toEuclideanLin (Aᴴ * A) (bV j.1)) := by
      rw [toEuclideanLin_gram, LinearMap.comp_apply, LinearMap.adjoint_inner_right]
    rw [inner_smul_left, inner_smul_right, hinner, hbV_eig j.1, inner_smul_right,
      orthonormal_iff_ite.mp bV.orthonormal i.1 j.1]
    simp only [Complex.conj_ofReal]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, mul_one]
      have hsq : lam i.1 = σ i.1 * σ i.1 := (Real.mul_self_sqrt (hG.eigenvalues_nonneg i.1)).symm
      rw [hsq]; push_cast; field_simp [Complex.ofReal_ne_zero.mpr hi_ne]
    · have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      simp [hij, hij']
  let W : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := Submodule.span ℂ (Set.range w)
  let bWperp := stdOrthonormalBasis ℂ Wᗮ
  have hcardW : Module.finrank ℂ W = S.card := by
    rw [finrank_span_eq_card hw_orth.linearIndependent, Fintype.card_coe]
  have hcardPerp : Module.finrank ℂ Wᗮ = Scomp.card := by
    have hsum := Submodule.finrank_add_finrank_orthogonal W
    rw [finrank_euclideanSpace_fin, hcardW] at hsum
    have hpart : S.card + Scomp.card = n := by
      have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
        (p := fun i => σ i ≠ 0)
      simpa [S, Scomp, not_not] using h1
    omega
  let ePerp : Scomp ≃ Fin (Module.finrank ℂ Wᗮ) :=
    Fintype.equivOfCardEq (by simp [hcardPerp])
  let uVec : Fin n → EuclideanSpace ℂ (Fin n) := fun i =>
    if hi : σ i ≠ 0 then w ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    else (bWperp (ePerp ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, not_not.mp hi⟩⟩) : EuclideanSpace ℂ (Fin n))
  have hu_orth : Orthonormal ℂ uVec := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hi : σ i ≠ 0 <;> by_cases hj : σ j ≠ 0
    · simp only [uVec, dif_pos hi, dif_pos hj]
      rw [orthonormal_iff_ite.mp hw_orth]
      by_cases hij : i = j <;> simp [hij]
    · simp only [uVec, dif_pos hi, dif_neg hj]
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      rw [if_neg hij]
      have hw_mem : w ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩ ∈ W :=
        Submodule.subset_span (Set.mem_range_self _)
      have hp_mem := (bWperp (ePerp ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, not_not.mp hj⟩⟩)).2
      exact Submodule.inner_right_of_mem_orthogonal hw_mem hp_mem
    · simp only [uVec, dif_neg hi, dif_pos hj]
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      rw [if_neg hij]
      have hw_mem : w ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩ ∈ W :=
        Submodule.subset_span (Set.mem_range_self _)
      have hp_mem := (bWperp (ePerp ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, not_not.mp hi⟩⟩)).2
      exact Submodule.inner_left_of_mem_orthogonal hw_mem hp_mem
    · simp only [uVec, dif_neg hi, dif_neg hj]
      change inner ℂ (bWperp _) (bWperp _) = _
      rw [orthonormal_iff_ite.mp bWperp.orthonormal]
      by_cases hij : i = j
      · subst hij; simp
      · have hne : ePerp ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, not_not.mp hi⟩⟩ ≠
            ePerp ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, not_not.mp hj⟩⟩ := by
          intro h
          exact hij (congrArg Subtype.val (ePerp.injective h))
        simp [hij, hne]
  have hAction : ∀ i : Fin n, Matrix.toEuclideanLin A (bV i) = (σ i : ℂ) • uVec i := by
    intro i
    by_cases hi : σ i ≠ 0
    · simp only [uVec, dif_pos hi, w, smul_smul]
      have h1 : (σ i : ℂ) * ((σ i)⁻¹ : ℝ) = 1 := by
        push_cast; exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hi)
      rw [h1, one_smul]
    · push Not at hi
      rw [hi, Complex.ofReal_zero, zero_smul]
      have hlam0 : lam i = 0 := by
        have hsq := Real.sq_sqrt (hG.eigenvalues_nonneg i)
        have h0 : σ i ^ 2 = 0 := by rw [hi]; ring
        linarith
      have hinner : inner ℂ (Matrix.toEuclideanLin A (bV i)) (Matrix.toEuclideanLin A (bV i)) = 0 := by
        rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, ← toEuclideanLin_gram,
          hbV_eig i, hlam0, Complex.ofReal_zero, zero_smul, inner_zero_right]
      exact inner_self_eq_zero.mp hinner
  -- Directly define Umat with columns uVec j!
  let Umat : Mat n := Matrix.of fun i j => (uVec j).ofLp i
  have hU_mem : Umat ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, Umat, Matrix.of_apply]
    have hinner := orthonormal_iff_ite.mp hu_orth i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
    simpa [dotProduct, mul_comm, eq_comm] using hinner
  let U : Matrix.unitaryGroup (Fin n) ℂ := ⟨Umat, hU_mem⟩
  have hEq : A = (U : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (V : Mat n)ᴴ := by
    apply Matrix.toEuclideanLin.injective
    apply bV.toBasis.ext
    intro k
    have hbk : bV.toBasis k = bV k := rfl
    rw [hbk, hAction k]
    apply WithLp.ofLp_injective
    ext j
    have hVcol : ∀ a b, (V : Mat n) a b = (bV b).ofLp a := fun a b => by
      simp [V, bV, Matrix.IsHermitian.eigenvectorUnitary_apply]
    have hVH_v : (V : Mat n)ᴴ.mulVec (bV k).ofLp = Pi.single k 1 := by
      ext i
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, hVcol, Pi.single_apply]
      have hinner := orthonormal_iff_ite.mp bV.orthonormal i k
      rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
      simpa [dotProduct, mul_comm, eq_comm] using hinner
    change ((σ k : ℂ) • uVec k).ofLp j =
      ((((U : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (V : Mat n)ᴴ).mulVec (bV k).ofLp) j)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hVH_v]
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, U, Umat, Pi.single_apply, mul_comm]
  refine ⟨U, V, σ, hσ_nn, hEq, fun p hp => ?_⟩
  let Vstar : Matrix.unitaryGroup (Fin n) ℂ := star V
  have hVstar : (Vstar : Mat n) = (V : Mat n)ᴴ := rfl
  rw [hEq, ← hVstar, schattenPow_unitary_mul_right hp.le, schattenPow_unitary_mul_left,
    schattenPow_diagonal hp σ hσ_nn]

/-- Polar decomposition A = W * |A| with unitary W. -/
theorem exists_polar_unitary {n : ℕ} (A : Mat n) :
    ∃ W : Matrix.unitaryGroup (Fin n) ℂ, A = (W : Mat n) * matAbs A := by
  obtain ⟨U, V, σ, hσ, hSVD, _⟩ := exists_svd A
  refine ⟨U * star V, ?_⟩
  have hP : matAbs A = (V : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (V : Mat n)ᴴ := by
    have hPD : ((V : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (V : Mat n)ᴴ).PosSemidef := by
      have hdiag : (Matrix.diagonal (fun i => (σ i : ℂ))).PosSemidef := by
        rw [Matrix.posSemidef_diagonal_iff]
        intro i; exact_mod_cast hσ i
      simpa using hdiag.mul_mul_conjTranspose_same (V : Mat n)
    apply matAbs_eq_of_posSemidef_sq hPD
    have hV : (V : Mat n)ᴴ * (V : Mat n) = 1 := unitary_conjTranspose_mul_self V
    have hU : (U : Mat n)ᴴ * (U : Mat n) = 1 := unitary_conjTranspose_mul_self U
    have hD : (Matrix.diagonal (fun i => (σ i : ℂ)))ᴴ = Matrix.diagonal (fun i => (σ i : ℂ)) := by
      ext i j; by_cases h : i = j
      · subst h; simp
      · simp [Matrix.diagonal, h, Ne.symm h]
    rw [hSVD]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
    have h1 : (V : Mat n) * (Matrix.diagonal (fun i => (σ i : ℂ)) *
        ((V : Mat n)ᴴ * ((V : Mat n) * (Matrix.diagonal (fun i => (σ i : ℂ)) * (V : Mat n)ᴴ)))) =
        (V : Mat n) * (Matrix.diagonal (fun i => (σ i : ℂ)) *
        (Matrix.diagonal (fun i => (σ i : ℂ)) * (V : Mat n)ᴴ)) := by
      rw [← Matrix.mul_assoc (V : Mat n)ᴴ (V : Mat n), hV, Matrix.one_mul]
    have h2 : (V : Mat n) * (Matrix.diagonal (fun i => (σ i : ℂ)) *
        ((U : Mat n)ᴴ * ((U : Mat n) * (Matrix.diagonal (fun i => (σ i : ℂ)) * (V : Mat n)ᴴ)))) =
        (V : Mat n) * (Matrix.diagonal (fun i => (σ i : ℂ)) *
        (Matrix.diagonal (fun i => (σ i : ℂ)) * (V : Mat n)ᴴ)) := by
      rw [← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n), hU, Matrix.one_mul]
    rw [h1, h2]
  rw [hP, hSVD]
  change (U : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (V : Mat n)ᴴ =
    ((U : Mat n) * (V : Mat n)ᴴ) * ((V : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (V : Mat n)ᴴ)
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (V : Mat n)ᴴ (V : Mat n), unitary_conjTranspose_mul_self V, Matrix.one_mul]

end MI20
