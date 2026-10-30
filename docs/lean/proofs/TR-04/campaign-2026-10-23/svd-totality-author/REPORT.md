# TR-04 rectangular SVD author evidence

`NLA.Proofs.TR04.SVD.exists_validSVD` proves the unchanged literal `SVDMachine.ValidSVD` relation for every real `Fin m × Fin l` matrix, with no dimension, rank or basis hypothesis. The full left and right factors are square orthogonal matrices; singular values are nonnegative and decreasing. Empty dimensions, rank zero and rectangular dimensions are covered by the single theorem.

The construction diagonalizes the real Gram operator in its ordered orthonormal eigenbasis. Positive normalized images form an orthonormal family in the codomain and are extended, at their original indices, to a full basis. Singular values outside the actual range rank vanish. Applying the basis expansion to each coordinate vector yields the exact rectangular reconstruction sum. The Gram norm argument adapts the prior RA-10 square proof to independent domain and codomain dimensions; RA-10 sources were not changed.

Run `python3 run-author.py` from this evidence directory, or from any directory. The runner hashes each locked source, compiles the actual machine model and both new modules afresh into private objects using the pinned local Lean 4.33.1 and read-only dependency packages, then compiles `ExactConsumer.lean` with the literal requested theorem type. All four commands returned zero; the consumer and public endpoint pass `#assert_trust kernel`, and printed axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.

This is author kernel evidence. It does not claim independent review, the full TR-04 Target, actual Linux CI, or Comparator validation. No canonical scaffold, Solution, Target, model, original problem, status, or ID was changed.
