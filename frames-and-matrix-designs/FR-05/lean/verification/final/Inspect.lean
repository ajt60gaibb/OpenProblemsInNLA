import Solution

open scoped Topology

-- Check the exact all-dimension quantitative target and original limit.
example : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
    NLA.FR05.phaseRetrievalProbability d ≤ C / d :=
  NLA.FR05.phaseRetrieval_injective_probability_le_inv

example : Filter.Tendsto NLA.FR05.phaseRetrievalProbability Filter.atTop (𝓝 0) :=
  NLA.FR05.phaseRetrieval_injective_probability_tendsto_zero

#print axioms NLA.FR05.sourcePlantedLikelihood_injective_probability
#print axioms NLA.FR05.phaseRetrieval_probability_le_planted_add_sqrt
#print axioms NLA.FR05.source_eventual_probability_comparison
#print axioms NLA.FR05.phaseRetrieval_injective_probability_le_inv
#print axioms NLA.FR05.phaseRetrieval_injective_probability_tendsto_zero
