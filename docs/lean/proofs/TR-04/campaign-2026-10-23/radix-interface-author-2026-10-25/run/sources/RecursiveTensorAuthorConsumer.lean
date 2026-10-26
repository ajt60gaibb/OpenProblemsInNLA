import NLA.Proofs.TR04.TensorCompressionRadixDecode
import NLA.Proofs.TR04.TTCompletionOriginal
import NLA.Proofs.TR04.TTCompletionProjected
import NLA.Proofs.TR04.TensorCompressionLinear
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace RecursiveTensorAuthorConsumer
open NLA.Computation.TensorTrainApproximation
open NLA.Proofs.TR04.TensorFormat
 theorem actual_original_completion (S : Shape) (r : Ranks S) (A : Tensor S) :
    ∃ X : Tensor S, (∀ j, Matrix.rank (Unfold S X j) ≤ r j) ∧
      FrobeniusSq S A X ≤ ((S.order - 1 : ℕ) : ℝ) *
        sInf {e : ℝ | ∃ Y : Tensor S,
          (∀ j, Matrix.rank (Unfold S Y j) ≤ r j) ∧ e = FrobeniusSq S A Y} ∧
      (Optimum S r A = 0 → X = A) := by
  obtain ⟨X, hX⟩ := original_completion_exists S r A
  exact ⟨X, original_completion_feasible hX, original_completion_optimum_bound hX,
    original_completion_exact_of_optimum_zero hX⟩
#assert_trust kernel actual_original_completion
#print axioms actual_original_completion
 theorem actual_literal_decode (S : Shape) (x : Index S) :
    Decode S (Offset S x) = x := original_decode_offset S x
 theorem actual_literal_encode (S : Shape) (address : ℕ) (h : address < DenseSize S) :
    Offset S (Decode S address) = address := original_offset_decode S address h
 theorem actual_input_cell (S : Shape) (r : Ranks S) (A : Tensor S) (x : Index S) :
    InputMemory S r A (2 * S.order - 1 + Offset S x) = A x :=
  original_inputMemory_tensor_cell S r A x
 theorem actual_SVD_right_transport {m l : ℕ} (B : Matrix (Fin m) (Fin l) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) (e : Fin l ≃ Fin l)
    (h : NLA.Computation.SVDMachine.ValidSVD B U sigma V) :
    NLA.Computation.SVDMachine.ValidSVD (B.submatrix id e) U sigma (V.submatrix e id) :=
  validSVD_reindex_columns h e
#assert_trust kernel actual_literal_decode
#assert_trust kernel actual_literal_encode
#assert_trust kernel actual_input_cell
#assert_trust kernel actual_SVD_right_transport
#print axioms actual_literal_decode
#print axioms actual_literal_encode
#print axioms actual_input_cell
#print axioms actual_SVD_right_transport
end RecursiveTensorAuthorConsumer
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.radixIndexEquiv
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixOffset
#print axioms NLA.Proofs.TR04.TensorFormat.radixOffset
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_symm_val
#print axioms NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_symm_val
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixOffset_lt
#print axioms NLA.Proofs.TR04.TensorFormat.radixOffset_lt
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_decode_encode
#print axioms NLA.Proofs.TR04.TensorFormat.radixIndexEquiv_decode_encode
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.cardToProdEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.cardToProdEquiv
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv_symm_val
#print axioms NLA.Proofs.TR04.TensorFormat.radixSuffixEquiv_symm_val
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.prod_modeList
#print axioms NLA.Proofs.TR04.TensorFormat.prod_modeList
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorSuffixSize
#print axioms NLA.Proofs.TR04.TensorFormat.vectorSuffixSize
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_zero
#print axioms NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_zero
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_succ
#print axioms NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_succ
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorOffset
#print axioms NLA.Proofs.TR04.TensorFormat.vectorOffset
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixOffset_vector
#print axioms NLA.Proofs.TR04.TensorFormat.radixOffset_vector
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_radixOffset
#print axioms NLA.Proofs.TR04.TensorFormat.original_radixOffset
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_offset_lt_denseSize
#print axioms NLA.Proofs.TR04.TensorFormat.original_offset_lt_denseSize
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.validSVD_reindex_columns
#print axioms NLA.Proofs.TR04.TensorFormat.validSVD_reindex_columns
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixDenseFirst
#print axioms NLA.Proofs.TR04.TensorFormat.radixDenseFirst
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.suffixPermutation
#print axioms NLA.Proofs.TR04.TensorFormat.suffixPermutation
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixDenseFirst_eq_reindex
#print axioms NLA.Proofs.TR04.TensorFormat.radixDenseFirst_eq_reindex
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.denseFirst_eq_reindex_radix
#print axioms NLA.Proofs.TR04.TensorFormat.denseFirst_eq_reindex_radix
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.rank_radixDenseFirst
#print axioms NLA.Proofs.TR04.TensorFormat.rank_radixDenseFirst
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.energy_radixDenseFirst
#print axioms NLA.Proofs.TR04.TensorFormat.energy_radixDenseFirst
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radix_validSVD_to_denseFirst
#print axioms NLA.Proofs.TR04.TensorFormat.radix_validSVD_to_denseFirst
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.completion_step_radix
#print axioms NLA.Proofs.TR04.TensorFormat.completion_step_radix
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.mode_suffix_dvd_prod
#print axioms NLA.Proofs.TR04.TensorFormat.mode_suffix_dvd_prod
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_pos
#print axioms NLA.Proofs.TR04.TensorFormat.vectorSuffixSize_pos
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorOffset_cons
#print axioms NLA.Proofs.TR04.TensorFormat.vectorOffset_cons
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.vectorOffset_digit
#print axioms NLA.Proofs.TR04.TensorFormat.vectorOffset_digit
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_decode_offset
#print axioms NLA.Proofs.TR04.TensorFormat.original_decode_offset
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.radixOffset_decode
#print axioms NLA.Proofs.TR04.TensorFormat.radixOffset_decode
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.denseToProdEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.denseToProdEquiv
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalRadixIndexEquiv
#print axioms NLA.Proofs.TR04.TensorFormat.originalRadixIndexEquiv
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.originalRadixIndexEquiv_offset
#print axioms NLA.Proofs.TR04.TensorFormat.originalRadixIndexEquiv_offset
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_offset_decode
#print axioms NLA.Proofs.TR04.TensorFormat.original_offset_decode
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_offset_injective
#print axioms NLA.Proofs.TR04.TensorFormat.original_offset_injective
#assert_trust kernel NLA.Proofs.TR04.TensorFormat.original_inputMemory_tensor_cell
#print axioms NLA.Proofs.TR04.TensorFormat.original_inputMemory_tensor_cell
