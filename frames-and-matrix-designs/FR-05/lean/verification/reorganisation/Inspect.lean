import Solution

open scoped Topology

-- The same quantitative target and original limit after module reorganisation.
example : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
    NLA.FR05.phaseRetrievalProbability d ≤ C / d :=
  NLA.FR05.phaseRetrieval_injective_probability_le_inv

example : Filter.Tendsto NLA.FR05.phaseRetrievalProbability Filter.atTop (𝓝 0) :=
  NLA.FR05.phaseRetrieval_injective_probability_tendsto_zero

#print axioms NLA.FR05.proposition_3_1
#print axioms NLA.FR05.proposition_3_1_haar
#print axioms NLA.FR05.proposition_3_2
#print axioms NLA.FR05.source_haar_planted_frame_law_eq_likelihood
#print axioms NLA.FR05.source_reference_frame_law_eq_likelihood
#print axioms NLA.FR05.source_reference_injective_probability
#print axioms NLA.FR05.phaseRetrieval_probability_le_planted_add_sqrt
#print axioms NLA.FR05.phaseRetrieval_injective_probability_le_inv
#print axioms NLA.FR05.phaseRetrieval_injective_probability_tendsto_zero
