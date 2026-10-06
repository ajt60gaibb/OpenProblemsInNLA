# Independent review of GaussianEliminationTail

Reviewer: source_statement_author, independent of implementation. Reviewed source SHA-256: cf512739f8e6ac950dc25841093fa2d87896b3664e39dd9fcb99bdfc53eb5160. The complete file was read.

The proof matches the exact preimplementation contract. For each stage k and fresh column j at least k, stage_column_tail uses the previously proved product joint law of the actual selectedRows operator and column j. The event is Borel measurable. Its fiber over the operator is bounded by the Gaussian row tail if that operator satisfies RowCap, and is empty otherwise. Integrating this bound against the operator's probability marginal produces the exact factor 2n. In particular, it does not condition the fresh Gaussian column on an event involving future stages.

guarded_raw_subset uses the all-stage cap only for set containment. The exact eliminationRows_mul identity turns each active Schur entry into the corresponding operator-row dot product with its original column. Testing the finite active maximum then yields a union of stage-column events; inactive stage-column pairs are empty. The finite union has n² pairs and gives exactly 2n³ exp(-x).

The final split separates failure of the actual canonical row norm bound, then applies the existing exact normalization bridge. Its conclusion retains the original exceedance event and adds the explicit q^(n²) denominator term. Zero dimension and zero variance cap cause no division issue or false strict event. No nonsingularity or admissibility assumption was added to the deterministic/fresh-column transfer.

No mathematical changes requested. This unconditional transfer reduces the main theorem to the probabilistic bound for badRowsEvent; it does not claim that remaining bound. Compilation and foundational-only kernel/axiom checks were reported by the implementing coordinator, and the mathematical source content was checked independently here.
