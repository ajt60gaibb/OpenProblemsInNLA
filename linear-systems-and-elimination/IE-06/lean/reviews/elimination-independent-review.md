# Independent exact-code review: elimination operators

Source SHA-256: `6130858793534d3964a62ade818f98c814424927e169dc4e1fc71e5816dfb8a0`. Reviewer: independent mathematical-review agent. Verdict: approved.

The operator starts at the identity, swaps the same current rows as the actual Schur recursion, subtracts the actual pivot multiplier times the pivot row, and zeros eliminated rows. Multiplication by the original matrix therefore reproduces every still-active trajectory column (j≥k), including stage zero. No identity is asserted for zeroed eliminated columns. Total division keeps the deterministic identities valid on invalid paths.

The row-l1 bound uses admissibility exactly where needed: the pivot is nonzero and has maximal magnitude among all active rows, so the swapped-row multiplier has absolute value at most one. Every row l1 norm is therefore at most 2^k; k=0 starts from identity, and out-of-range stages are zero.

The prefix-dependence theorem is explicitly for a fixed path. ColumnsAgree means agreement in original columns j<d; at a step k<d the only extra column used by a Schur or left-operator update is the pivot column k, so the induction hypothesis provides exactly the required information. The canonical data-dependent path factorization remains separate work in PivotFiltration. All dimensions, including zero, are covered. No probabilistic assertion or orthogonality is assumed or concluded here.

Semantic/code review is separate from the recorded root compilation and whole-package immutable verification.
