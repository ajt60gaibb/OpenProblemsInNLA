import NLA.Proofs.TR04.TensorCompressionRadixSVD
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix

namespace NLA.Proofs.TR04.TensorFormat

/-- A mode together with every following suffix factor divides the whole product. -/
theorem mode_suffix_dvd_prod {d : ℕ} (n : Fin d → ℕ) (i : Fin d) :
    n i * vectorSuffixSize n i ∣ (modeList n).prod := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [vectorSuffixSize_zero]
      exact dvd_refl _
    · rw [vectorSuffixSize_succ]
      obtain ⟨c, hc⟩ := ih (fun i : Fin d => n i.succ) i
      refine ⟨n 0 * c, ?_⟩
      change n 0 * (modeList (fun i : Fin d => n i.succ)).prod = _
      rw [hc]
      ring

theorem vectorSuffixSize_pos {d : ℕ} (n : Fin d → ℕ)
    (x : (i : Fin d) → Fin (n i)) (i : Fin d) : 0 < vectorSuffixSize n i := by
  have hp : 0 < (modeList n).prod :=
    lt_of_le_of_lt (Nat.zero_le _) (radixOffset_lt _ ((vectorIndexEquiv n).symm x))
  have hd := mode_suffix_dvd_prod n i
  by_contra hn
  have hz : vectorSuffixSize n i = 0 := Nat.eq_zero_of_not_pos hn
  rw [hz, Nat.mul_zero] at hd
  have hzero : (modeList n).prod = 0 := zero_dvd_iff.mp hd
  omega

theorem vectorOffset_cons {d : ℕ} (n : Fin (d + 1) → ℕ)
    (x : (i : Fin (d + 1)) → Fin (n i)) :
    vectorOffset n x = (x 0).val * (modeList (fun i : Fin d => n i.succ)).prod +
      vectorOffset (fun i : Fin d => n i.succ) (Fin.tail x) := by
  simp only [vectorOffset, Fin.sum_univ_succ, vectorSuffixSize_zero,
    vectorSuffixSize_succ, Fin.tail]

/-- Exact mixed-radix digit recovery, for any finite vector that has an index. -/
theorem vectorOffset_digit {d : ℕ} (n : Fin d → ℕ) (x : (i : Fin d) → Fin (n i))
    (i : Fin d) : (vectorOffset n x / vectorSuffixSize n i) % n i = (x i).val := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    let nt : Fin d → ℕ := fun i => n i.succ
    let xt : (i : Fin d) → Fin (nt i) := Fin.tail x
    refine Fin.cases ?_ (fun i => ?_) i
    · have htail : vectorOffset nt xt < (modeList nt).prod := by
        rw [← radixOffset_vector]
        exact radixOffset_lt _ _
      have hpos : 0 < (modeList nt).prod := lt_of_le_of_lt (Nat.zero_le _) htail
      rw [vectorOffset_cons, vectorSuffixSize_zero]
      change (((x 0).val * (modeList nt).prod + vectorOffset nt xt) /
        (modeList nt).prod) % n 0 = (x 0).val
      rw [Nat.add_comm ((x 0).val * (modeList nt).prod) (vectorOffset nt xt),
        Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt htail, Nat.zero_add]
      exact Nat.mod_eq_of_lt (x 0).isLt
    · have hs : 0 < vectorSuffixSize nt i := vectorSuffixSize_pos nt xt i
      obtain ⟨c, hc⟩ := mode_suffix_dvd_prod nt i
      have he : (x 0).val * (modeList nt).prod + vectorOffset nt xt =
          vectorOffset nt xt + ((x 0).val * nt i * c) * vectorSuffixSize nt i := by
        rw [hc]
        ring
      rw [vectorOffset_cons, vectorSuffixSize_succ]
      change (((x 0).val * (modeList nt).prod + vectorOffset nt xt) /
        vectorSuffixSize nt i) % nt i = (xt i).val
      rw [he, Nat.add_mul_div_right _ _ hs]
      simpa [Nat.add_mod, Nat.mul_mod] using ih nt xt i

/-- The immutable literal digit decoder recovers every original index. -/
theorem original_decode_offset (S : NLA.Computation.TensorTrainApproximation.Shape)
    (x : NLA.Computation.TensorTrainApproximation.Index S) :
    NLA.Computation.TensorTrainApproximation.Decode S
      (NLA.Computation.TensorTrainApproximation.Offset S x) = x := by
  funext i
  apply Fin.ext
  exact vectorOffset_digit S.mode x i

@[simp] theorem radixOffset_decode (ns : List ℕ) (i : Fin ns.prod) :
    radixOffset ns (radixIndexEquiv ns i) = i.val := by
  have h := radixIndexEquiv_symm_val ns (radixIndexEquiv ns i)
  simpa only [Equiv.symm_apply_apply] using h.symm

def denseToProdEquiv (S : NLA.Computation.TensorTrainApproximation.Shape) :
    Fin (NLA.Computation.TensorTrainApproximation.DenseSize S) ≃ Fin (modeList S.mode).prod where
  toFun i := ⟨i.val, by rw [prod_modeList]; exact i.isLt⟩
  invFun i := ⟨i.val, by change i.val < ∏ j, S.mode j; rw [← prod_modeList]; exact i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

def originalRadixIndexEquiv (S : NLA.Computation.TensorTrainApproximation.Shape) :
    Fin (NLA.Computation.TensorTrainApproximation.DenseSize S) ≃
      NLA.Computation.TensorTrainApproximation.Index S :=
  ((denseToProdEquiv S).trans (radixIndexEquiv (modeList S.mode))).trans
    (vectorIndexEquiv S.mode)

theorem originalRadixIndexEquiv_offset (S : NLA.Computation.TensorTrainApproximation.Shape)
    (i : Fin (NLA.Computation.TensorTrainApproximation.DenseSize S)) :
    NLA.Computation.TensorTrainApproximation.Offset S (originalRadixIndexEquiv S i) = i.val := by
  rw [← original_radixOffset]
  change radixOffset (modeList S.mode)
    ((vectorIndexEquiv S.mode).symm ((vectorIndexEquiv S.mode)
      (radixIndexEquiv (modeList S.mode) (denseToProdEquiv S i)))) = i.val
  rw [Equiv.symm_apply_apply, radixOffset_decode]
  rfl

/-- Every valid dense address is used, with no collisions or skipped entries. -/
theorem original_offset_decode (S : NLA.Computation.TensorTrainApproximation.Shape)
    (address : ℕ) (h : address < NLA.Computation.TensorTrainApproximation.DenseSize S) :
    NLA.Computation.TensorTrainApproximation.Offset S
      (NLA.Computation.TensorTrainApproximation.Decode S address) = address := by
  let i : Fin (NLA.Computation.TensorTrainApproximation.DenseSize S) := ⟨address, h⟩
  have he := originalRadixIndexEquiv_offset S i
  change NLA.Computation.TensorTrainApproximation.Offset S (originalRadixIndexEquiv S i) = address at he
  rw [← he, original_decode_offset]

theorem original_offset_injective (S : NLA.Computation.TensorTrainApproximation.Shape) :
    Function.Injective (NLA.Computation.TensorTrainApproximation.Offset S) := by
  intro x y h
  have hh := congrArg (NLA.Computation.TensorTrainApproximation.Decode S) h
  simpa only [original_decode_offset] using hh

/-- The actual original input-memory tensor cell at its literal output offset. -/
theorem original_inputMemory_tensor_cell (S : NLA.Computation.TensorTrainApproximation.Shape)
    (r : NLA.Computation.TensorTrainApproximation.Ranks S)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S)
    (x : NLA.Computation.TensorTrainApproximation.Index S) :
    NLA.Computation.TensorTrainApproximation.InputMemory S r A
      (2 * S.order - 1 + NLA.Computation.TensorTrainApproximation.Offset S x) = A x := by
  have hd := S.order_ge
  have hbound := original_offset_lt_denseSize S x
  have hfirst : ¬ 2 * S.order - 1 + NLA.Computation.TensorTrainApproximation.Offset S x < S.order := by omega
  have hrank : ¬ (2 * S.order - 1 + NLA.Computation.TensorTrainApproximation.Offset S x) - S.order <
      S.order - 1 := by omega
  simp only [NLA.Computation.TensorTrainApproximation.InputMemory, dif_neg hfirst, dif_neg hrank,
    Nat.add_sub_cancel_left, if_pos hbound, original_decode_offset]

#assert_trust kernel vectorOffset_digit
#assert_trust kernel original_decode_offset
#assert_trust kernel originalRadixIndexEquiv
#assert_trust kernel originalRadixIndexEquiv_offset
#assert_trust kernel original_offset_decode
#assert_trust kernel original_offset_injective
#assert_trust kernel original_inputMemory_tensor_cell
#print axioms original_decode_offset
#print axioms original_inputMemory_tensor_cell
end NLA.Proofs.TR04.TensorFormat
