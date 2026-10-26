import NLA.Proofs.RE06.GaussianRangeFinderMoment

set_option autoImplicit false
set_option leancert.trust "kernel"

open Lean Elab Command in
elab "#gaussian_actual_theorem " n:ident : command => do
  let d ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? d with
  | some (.thmInfo _) => pure ()
  | _ => throwErrorAt n "expected an actual theorem declaration"

open Lean Elab Command in
elab "#gaussian_function_definition " n:ident : command => do
  let d ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? d with
  | some (.defnInfo _) => pure ()
  | _ => throwErrorAt n "expected a functional definition declaration"

#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_linear_memLp
#assert_trust kernel NLA.Proofs.RE06.gaussian_linear_memLp
#print axioms NLA.Proofs.RE06.gaussian_linear_memLp
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_linear_mean
#assert_trust kernel NLA.Proofs.RE06.gaussian_linear_mean
#print axioms NLA.Proofs.RE06.gaussian_linear_mean
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_linear_square_integrable
#assert_trust kernel NLA.Proofs.RE06.gaussian_linear_square_integrable
#print axioms NLA.Proofs.RE06.gaussian_linear_square_integrable
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_linear_square_integral
#assert_trust kernel NLA.Proofs.RE06.gaussian_linear_square_integral
#print axioms NLA.Proofs.RE06.gaussian_linear_square_integral
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_product_entry
#assert_trust kernel NLA.Proofs.RE06.gaussian_product_entry
#print axioms NLA.Proofs.RE06.gaussian_product_entry
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_product_square_eq_sum
#assert_trust kernel NLA.Proofs.RE06.gaussian_product_square_eq_sum
#print axioms NLA.Proofs.RE06.gaussian_product_square_eq_sum
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_product_square_integrable
#assert_trust kernel NLA.Proofs.RE06.gaussian_product_square_integrable
#print axioms NLA.Proofs.RE06.gaussian_product_square_integrable
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_product_square_integral
#assert_trust kernel NLA.Proofs.RE06.gaussian_product_square_integral
#print axioms NLA.Proofs.RE06.gaussian_product_square_integral
#gaussian_actual_theorem NLA.Proofs.RE06.hasLaw_gaussian_product_square_integrable
#assert_trust kernel NLA.Proofs.RE06.hasLaw_gaussian_product_square_integrable
#print axioms NLA.Proofs.RE06.hasLaw_gaussian_product_square_integrable
#gaussian_actual_theorem NLA.Proofs.RE06.hasLaw_gaussian_product_square_integral
#assert_trust kernel NLA.Proofs.RE06.hasLaw_gaussian_product_square_integral
#print axioms NLA.Proofs.RE06.hasLaw_gaussian_product_square_integral
#gaussian_actual_theorem NLA.Proofs.RE06.stream_gaussian_product_square_integrable
#assert_trust kernel NLA.Proofs.RE06.stream_gaussian_product_square_integrable
#print axioms NLA.Proofs.RE06.stream_gaussian_product_square_integrable
#gaussian_actual_theorem NLA.Proofs.RE06.stream_gaussian_product_square_integral
#assert_trust kernel NLA.Proofs.RE06.stream_gaussian_product_square_integral
#print axioms NLA.Proofs.RE06.stream_gaussian_product_square_integral
#gaussian_actual_theorem NLA.Proofs.RE06.measurable_gaussian_product_energy
#assert_trust kernel NLA.Proofs.RE06.measurable_gaussian_product_energy
#print axioms NLA.Proofs.RE06.measurable_gaussian_product_energy
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_product_fubini_integrable
#assert_trust kernel NLA.Proofs.RE06.gaussian_product_fubini_integrable
#print axioms NLA.Proofs.RE06.gaussian_product_fubini_integrable
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_product_fubini_integral
#assert_trust kernel NLA.Proofs.RE06.gaussian_product_fubini_integral
#print axioms NLA.Proofs.RE06.gaussian_product_fubini_integral
#gaussian_actual_theorem NLA.Proofs.RE06.hasLaw_gaussian_product_fubini_integrable
#assert_trust kernel NLA.Proofs.RE06.hasLaw_gaussian_product_fubini_integrable
#print axioms NLA.Proofs.RE06.hasLaw_gaussian_product_fubini_integrable
#gaussian_actual_theorem NLA.Proofs.RE06.hasLaw_gaussian_product_fubini_integral
#assert_trust kernel NLA.Proofs.RE06.hasLaw_gaussian_product_fubini_integral
#print axioms NLA.Proofs.RE06.hasLaw_gaussian_product_fubini_integral
#gaussian_actual_theorem NLA.Proofs.RE06.independent_gaussian_product_fubini_integral
#assert_trust kernel NLA.Proofs.RE06.independent_gaussian_product_fubini_integral
#print axioms NLA.Proofs.RE06.independent_gaussian_product_fubini_integral
#gaussian_function_definition NLA.Proofs.RE06.gaussianTailRow
#assert_trust kernel NLA.Proofs.RE06.gaussianTailRow
#print axioms NLA.Proofs.RE06.gaussianTailRow
#gaussian_function_definition NLA.Proofs.RE06.gaussianRowIndexEquiv
#assert_trust kernel NLA.Proofs.RE06.gaussianRowIndexEquiv
#print axioms NLA.Proofs.RE06.gaussianRowIndexEquiv
#gaussian_function_definition NLA.Proofs.RE06.gaussianHeadEntries
#assert_trust kernel NLA.Proofs.RE06.gaussianHeadEntries
#print axioms NLA.Proofs.RE06.gaussianHeadEntries
#gaussian_function_definition NLA.Proofs.RE06.gaussianTailEntries
#assert_trust kernel NLA.Proofs.RE06.gaussianTailEntries
#print axioms NLA.Proofs.RE06.gaussianTailEntries
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_row_split_hasLaw
#assert_trust kernel NLA.Proofs.RE06.gaussian_row_split_hasLaw
#print axioms NLA.Proofs.RE06.gaussian_row_split_hasLaw
#gaussian_actual_theorem NLA.Proofs.RE06.hasLaw_gaussian_row_split
#assert_trust kernel NLA.Proofs.RE06.hasLaw_gaussian_row_split
#print axioms NLA.Proofs.RE06.hasLaw_gaussian_row_split
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_head_entries_hasLaw
#assert_trust kernel NLA.Proofs.RE06.gaussian_head_entries_hasLaw
#print axioms NLA.Proofs.RE06.gaussian_head_entries_hasLaw
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_tail_entries_hasLaw
#assert_trust kernel NLA.Proofs.RE06.gaussian_tail_entries_hasLaw
#print axioms NLA.Proofs.RE06.gaussian_tail_entries_hasLaw
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_head_tail_independent
#assert_trust kernel NLA.Proofs.RE06.gaussian_head_tail_independent
#print axioms NLA.Proofs.RE06.gaussian_head_tail_independent
#gaussian_function_definition NLA.Proofs.RE06.gaussianWeightedTail
#assert_trust kernel NLA.Proofs.RE06.gaussianWeightedTail
#print axioms NLA.Proofs.RE06.gaussianWeightedTail
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_tail_row_eq_self
#assert_trust kernel NLA.Proofs.RE06.gaussian_tail_row_eq_self
#print axioms NLA.Proofs.RE06.gaussian_tail_row_eq_self
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_tail_row_injective
#assert_trust kernel NLA.Proofs.RE06.gaussian_tail_row_injective
#print axioms NLA.Proofs.RE06.gaussian_tail_row_injective
#gaussian_actual_theorem NLA.Proofs.RE06.gaussianWeightedTail_energy
#assert_trust kernel NLA.Proofs.RE06.gaussianWeightedTail_energy
#print axioms NLA.Proofs.RE06.gaussianWeightedTail_energy
#gaussian_actual_theorem NLA.Proofs.RE06.gaussianWeightedTail_mul_entries
#assert_trust kernel NLA.Proofs.RE06.gaussianWeightedTail_mul_entries
#print axioms NLA.Proofs.RE06.gaussianWeightedTail_mul_entries
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_head_entries_matrix
#assert_trust kernel NLA.Proofs.RE06.gaussian_head_entries_matrix
#print axioms NLA.Proofs.RE06.gaussian_head_entries_matrix
#gaussian_actual_theorem NLA.Proofs.RE06.tailRandomEnergy_eq_split_product
#assert_trust kernel NLA.Proofs.RE06.tailRandomEnergy_eq_split_product
#print axioms NLA.Proofs.RE06.tailRandomEnergy_eq_split_product
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_pseudoinverse_energy_integrable
#assert_trust kernel NLA.Proofs.RE06.gaussian_pseudoinverse_energy_integrable
#print axioms NLA.Proofs.RE06.gaussian_pseudoinverse_energy_integrable
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_pseudoinverse_energy_integral
#assert_trust kernel NLA.Proofs.RE06.gaussian_pseudoinverse_energy_integral
#print axioms NLA.Proofs.RE06.gaussian_pseudoinverse_energy_integral
#gaussian_actual_theorem NLA.Proofs.RE06.measurable_gaussian_pseudoinverse_entries
#assert_trust kernel NLA.Proofs.RE06.measurable_gaussian_pseudoinverse_entries
#print axioms NLA.Proofs.RE06.measurable_gaussian_pseudoinverse_entries
#gaussian_actual_theorem NLA.Proofs.RE06.gaussian_split_rangefinder_moment
#assert_trust kernel NLA.Proofs.RE06.gaussian_split_rangefinder_moment
#print axioms NLA.Proofs.RE06.gaussian_split_rangefinder_moment
#gaussian_actual_theorem NLA.Proofs.RE06.headCoordinates_eq_gaussian_entries
#assert_trust kernel NLA.Proofs.RE06.headCoordinates_eq_gaussian_entries
#print axioms NLA.Proofs.RE06.headCoordinates_eq_gaussian_entries
#gaussian_actual_theorem NLA.Proofs.RE06.hasLaw_rangefinder_head_right_inverse_ae
#assert_trust kernel NLA.Proofs.RE06.hasLaw_rangefinder_head_right_inverse_ae
#print axioms NLA.Proofs.RE06.hasLaw_rangefinder_head_right_inverse_ae
#gaussian_actual_theorem NLA.Proofs.RE06.hasLaw_rangefinder_tail_moment
#assert_trust kernel NLA.Proofs.RE06.hasLaw_rangefinder_tail_moment
#print axioms NLA.Proofs.RE06.hasLaw_rangefinder_tail_moment
#gaussian_actual_theorem NLA.Proofs.RE06.stream_rangefinder_tail_moment
#assert_trust kernel NLA.Proofs.RE06.stream_rangefinder_tail_moment
#print axioms NLA.Proofs.RE06.stream_rangefinder_tail_moment
#gaussian_actual_theorem NLA.Proofs.RE06.stream_rangefinder_head_right_inverse_ae
#assert_trust kernel NLA.Proofs.RE06.stream_rangefinder_head_right_inverse_ae
#print axioms NLA.Proofs.RE06.stream_rangefinder_head_right_inverse_ae
