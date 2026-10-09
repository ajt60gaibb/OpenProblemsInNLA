# TR-14 independent preimplementation specification review

Reviewer: `/root/infra_audit`, an OpenAI Codex AI agent independent of the target specification author. Phase: specification. Verdict: **approve**.

I read the complete canonical README and exact specification and independently checked the mathematical representation before target Lean implementation. Infrastructure authorship does not make this reviewer an author of these problem specifications.

Zero-based tensor coordinates on Fin n convert the original sum of one-based indices minus m exactly into the sum of index values. The maximum index is m*(n-1), within the stipulated h length. All m>=3 and n>=2 and all complex data, including zero and exceptional tensors, remain quantified.

Ordinary terms use separate vectors for every mode, while symmetric terms use a single repeated vector and a complex coefficient. The coordinate sums/products are multilinear with no conjugation or normalization. No Vandermonde restriction is imposed on admissible decompositions.

Both width predicates are upward closed by padding with zero terms. A symmetric width-r decomposition gives an ordinary width-r decomposition by putting its coefficient into the first mode. Empty sums at r=0 give exactly zero on both sides.

The rank minima are well-defined. An ordinary decomposition exists by the coordinate basis expansion. For the Hankel symmetric decomposition, writing D=m*(n-1), choose D+1 distinct complex scalars: their Vandermonde moment vectors span C^(D+1), so h is a linear combination of them and H is the corresponding combination of (1,t,...,t^(n-1)) tensor powers. Hence equality of the minima is equivalent to equality of both upward-closed width predicates for every natural r, as proposed.

This does not add the stronger rank formula appearing in the resolution and does not assume the open target as an auxiliary hypothesis. The original full README is preserved byte for byte; index-bound handling and finite-coordinate implementation still need Lean boundary review.

This approval is specific to the following bytes and establishes specification fidelity only. It does not certify the cited resolution, a Lean proof, human peer review, or Linux Comparator execution. The implemented boundary still requires independent review.

- `tensor-computations/TR-14/README.md`: `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86`
- `docs/lean/statements/TR-14/NUMERICAL_TARGETS.md`: `6c50aa83745fc3d096e08b476fb08a841ffc0fefb2cdd58511f924c49f09da17`
- `docs/lean/statements/TR-14/ORIGINAL.md`: `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86`
