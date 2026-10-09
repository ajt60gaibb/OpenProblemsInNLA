# PF-04 independent preimplementation specification review

Reviewer: `/root/infra_audit`, an OpenAI Codex AI agent independent of the target specification author. Phase: specification. Verdict: **approve**.

I read the complete canonical README and exact specification and independently checked the proposed mathematical representation before any target Lean implementation. Infrastructure authorship does not make this reviewer an author of these problem specifications.

The real Gram-factor predicate explicitly requires entrywise nonnegative B and exact entry equalities Aij = sum_k Bik Bjk. Quantification over finite natural widths, including width zero with empty sums, is the original completely-positive cone; symmetry follows without imposing additional restrictions.

The universal width-nine factor assertion is the exact padded-column version of at most nine nonnegative rank-one summands. Zero columns permit every smaller width and do not exclude singular or zero inputs.

The separate CP witness having no factor of any width r < 9 preserves the displayed maximum-equals-nine formulation. Combined with the universal width-nine part it expresses both existence and sharpness of that maximum, without assuming the lower bound as an axiom.

No positive-definite, positive-entry, support, boundary-face, approximate, or algorithmic restriction was added. Zero A is correctly included but cannot satisfy the sharpness witness. The complete canonical README, including historical and author provenance, is preserved byte for byte.

This approval applies only to the input bytes below. It verifies statement fidelity, not truth of the conjecture or cited resolution, human peer review, a Lean boundary, or Linux Comparator execution. The implemented definitions still require independent boundary review.

- `nonnegative-and-positive-factorizations/PF-04/README.md`: `acbf30a432e4ee1898661c05a9efc2f24f9ec32183da33836315b58e6c46e08a`
- `docs/lean/statements/PF-04/NUMERICAL_TARGETS.md`: `3294326a93bf021afac3caae3349b01e6f5c23425060cbc22c8cba8c08af1e02`
- `docs/lean/statements/PF-04/ORIGINAL.md`: `acbf30a432e4ee1898661c05a9efc2f24f9ec32183da33836315b58e6c46e08a`
