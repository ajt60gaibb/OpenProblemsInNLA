# RA-10 transpose singular values: independent final review

**Disposition:** approved for aggregate import as the exact pointwise transpose gate. Nuclear-norm transpose, operator-norm transpose, right ideal, Eq. (14), and full RA-10 Target remain separate stages.

I independently inspected `NuclearSingularValuesTranspose.lean` at SHA-256 `92c4f19a3be7dcadcdbc3e60bd53ad8db33dd5dda799d1de0a31635a49a6a197` against the independently approved right-ideal precontract and frozen `Statements/RA10.lean`. The public theorem equates the **actual** `Matrix.toEuclideanLin` singular values of real `M.transpose` and `M` at each exact zero-based `i.val : ℕ` for every `i:Fin n`, including tied/zero values and `Fin 0`.

The two Gram matrices are respectively `MMᵀ` and `MᵀM`. Pinned `Matrix.charpoly_mul_comm` proves equal characteristic polynomials; pinned Hermitian eigenvalue uniqueness gives equality at each matrix index. The source then applies the same explicit `sortedHermitianIndex` to both sides, identifies those eigenvalues with the square of the corresponding singular value by the literal Euclidean Gram operator, and cancels squares using nonnegativity. There is no appeal to an unordered multiset, no matrix-order reversal, and no dimension factor.

Separate imported audit `/private/tmp/ra10-sv-transpose-independent-audit.lean` at SHA-256 `f460c85ee6bb4cc195ba9cbd151d0b889922199d08ccb4e8d2c09a5ab72feba3` restated the exact public signature and passed pinned Lean 4.33.1 with LeanCert `kernel`. `#assert_trust` passed; `#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound`. Source scan found no `sorry`, `admit`, `native_decide`, `unsafe`, or custom axiom.
