/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/recover_published_coverage.

Original question: Audenaert and Kittaneh. Complete analytic resolution:
Sidney Holden, Center for Computational Biology, Flatiron Institute,
Simons Foundation. The retained MI24 sources and their earlier MI22 bridge
retain their mathematical and code credits. The half-power/square-root bridge
uses the same pinned Mathlib API as MI24 SpectralPowers, without its strict
positivity hypotheses: the present witness includes singular and zero K.

UNCOMPILED AUTHOR DRAFT. No Lean process was run by this file's author.
The frozen traceNorm is never redefined or replaced. The nonnegative cfc(abs) K
is proved to square to the literal Gram matrix, so square-root uniqueness
identifies the actual CFC.rpow(Gram,1/2). C02 computes its real trace. The sign
function is zero on the kernel and bounded by one on every real eigenvalue.
-/
import NLA.MI27.SpectralSemantics
import NLA.MI27.PositiveTrace
import Mathlib.Data.Real.Sign
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

/-- Scalar identity includes x=0, hence includes every kernel eigenvalue. -/
lemma c18_sign_mul_self (x : ℝ) : Real.sign x * x = |x| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx, neg_one_mul, abs_of_neg hx]
  · simp only [Real.sign_zero, mul_zero, abs_zero]
  · rw [Real.sign_of_pos hx, one_mul, abs_of_pos hx]

lemma c18_norm_sign_le_one (x : ℝ) : ‖Real.sign x‖ ≤ 1 := by
  rcases Real.sign_apply_eq x with hx | hx | hx <;> simp only [hx, norm_neg,
    norm_one, norm_zero, zero_le_one, le_refl]

/-- The candidate absolute value is an actual nonnegative CFC matrix. -/
lemma c18_absolute_cfc_nonneg {n : ℕ} (K : Mat n) :
    0 ≤ cfc (fun x : ℝ => |x|) K :=
  cfc_nonneg fun x _ => abs_nonneg x

/-- CFC multiplication proves its square is the literal Gram matrix.
Neither invertibility nor positivity of K is assumed. -/
lemma c18_absolute_cfc_mul_self {n : ℕ} (K : Mat n) (hK : K.IsHermitian) :
    cfc (fun x : ℝ => |x|) K * cfc (fun x : ℝ => |x|) K = Kᴴ * K := by
  have ha : ContinuousOn (fun x : ℝ => |x|) (spectrum ℝ K) :=
    K.finite_real_spectrum.continuousOn _
  have hi : ContinuousOn (id : ℝ → ℝ) (spectrum ℝ K) :=
    K.finite_real_spectrum.continuousOn _
  calc
    cfc (fun x : ℝ => |x|) K * cfc (fun x : ℝ => |x|) K =
        cfc (fun x : ℝ => |x| * |x|) K :=
      (cfc_mul (fun x : ℝ => |x|) (fun x : ℝ => |x|) K ha ha).symm
    _ = cfc (fun x : ℝ => x * x) K := by
      apply cfc_congr
      intro x _
      simpa only [pow_two] using sq_abs x
    _ = cfc (id : ℝ → ℝ) K * cfc (id : ℝ → ℝ) K := by
      simpa only [id_eq] using cfc_mul (id : ℝ → ℝ) (id : ℝ → ℝ) K hi hi
    _ = Kᴴ * K := by
      simp only [cfc_id ℝ K hK.isSelfAdjoint, hK.eq]

/-- The actual square-root/absolute spectral bridge required by the frozen definition. -/
lemma c18_gram_half_eq_absolute_cfc {n : ℕ} (K : Mat n) (hK : K.IsHermitian) :
    CFC.rpow (Kᴴ * K) (1 / 2 : ℝ) = cfc (fun x : ℝ => |x|) K := by
  calc
    CFC.rpow (Kᴴ * K) (1 / 2 : ℝ) = CFC.sqrt (Kᴴ * K) :=
      (CFC.sqrt_eq_rpow (a := Kᴴ * K)).symm
    _ = cfc (fun x : ℝ => |x|) K :=
      CFC.sqrt_unique (c18_absolute_cfc_mul_self K hK) (c18_absolute_cfc_nonneg K)

/-- C02 identifies the unchanged Gram-square-root trace norm with the full
sum of absolute eigenvalues, retaining repeated and zero eigenvalues. -/
lemma c18_traceNorm_eq_sum_abs {n : ℕ} (hn : 1 ≤ n) (K : Mat n)
    (hK : K.IsHermitian) :
    traceNorm K = ∑ i : Fin n, |hK.eigenvalues i| := by
  unfold traceNorm
  rw [c18_gram_half_eq_absolute_cfc K hK]
  exact (spectral_function_semantics hn K hK (fun x : ℝ => |x|)
    (K.finite_real_spectrum.continuousOn _)).2.1

/-- The finite-spectrum CFC is legitimate even when sign is discontinuous at zero. -/
lemma c18_sign_cfc_mul {n : ℕ} (K : Mat n) (hK : K.IsHermitian) :
    cfc Real.sign K * K = cfc (fun x : ℝ => |x|) K := by
  have hs : ContinuousOn Real.sign (spectrum ℝ K) :=
    K.finite_real_spectrum.continuousOn _
  have hi : ContinuousOn (id : ℝ → ℝ) (spectrum ℝ K) :=
    K.finite_real_spectrum.continuousOn _
  calc
    cfc Real.sign K * K = cfc Real.sign K * cfc (id : ℝ → ℝ) K := by
      rw [cfc_id ℝ K hK.isSelfAdjoint]
    _ = cfc (fun x : ℝ => Real.sign x * x) K := by
      simpa only [id_eq] using (cfc_mul Real.sign (id : ℝ → ℝ) K hs hi).symm
    _ = cfc (fun x : ℝ => |x|) K := by
      apply cfc_congr
      intro x _
      exact c18_sign_mul_self x

/-- The scoped matrix norm is the frozen Euclidean operator norm. -/
lemma c18_sign_cfc_opNorm_le_one {n : ℕ} (K : Mat n) :
    opNorm (cfc Real.sign K) ≤ 1 := by
  rw [opNorm_eq_l2]
  exact norm_cfc_le zero_le_one fun x _ => c18_norm_sign_le_one x

/-- C18. Exact frozen witness contract; H is the spectral sign, with sign zero
on the kernel. The proof uses no division by a norm and includes K=0. -/
theorem hermitian_trace_norm_witness {n : ℕ} (hn : 1 ≤ n) (K : Mat n)
    (hK : K.IsHermitian) :
    ∃ H : Mat n, H.IsHermitian ∧ opNorm H ≤ 1 ∧ trR (H * K) = traceNorm K := by
  refine ⟨cfc Real.sign K, (cfc_predicate Real.sign K).isHermitian,
    c18_sign_cfc_opNorm_le_one K, ?_⟩
  calc
    trR (cfc Real.sign K * K) = trR (cfc (fun x : ℝ => |x|) K) :=
      congrArg trR (c18_sign_cfc_mul K hK)
    _ = ∑ i : Fin n, |hK.eigenvalues i| :=
      (spectral_function_semantics hn K hK (fun x : ℝ => |x|)
        (K.finite_real_spectrum.continuousOn _)).2.1
    _ = traceNorm K := (c18_traceNorm_eq_sum_abs hn K hK).symm

#print axioms hermitian_trace_norm_witness

end NLA.MI27
