# Canonical pivot filtration and fresh Gaussian columns: proposed exact contract

This bounded supporting module will use the actual deterministic `firstPivotIndex`, `firstTrajectory`, `firstPath`, and the exact `eliminationRows` from the reviewed definitions. It introduces no arbitrary selection rule or stochastic hypothesis.

For k∈ℕ, define `pastMatrix k A i j = if j.val < k then A i j else 0` and `selectedRows A k = eliminationRows A (firstPath A) k`. A fixed input column j is `column j A i = A i j`.

The proposed unconditional deterministic and measurable conclusions are:

1. If A and B agree in columns j<k, then their first s completed pivot choices agree for every s<k; their firstTrajectory at every stage s≤k agrees in columns j<k. These hold for singular matrices and total real division. The next pivot at stage k is deliberately not claimed to depend on only k columns.
2. If A and B agree in columns j<k then `selectedRows A k = selectedRows B k`, for every k (including k=0 and stages at/after n). Equivalently `selectedRows A k = selectedRows (pastMatrix k A) k`.
3. The maps `S ↦ firstPivotIndex S k`, `A ↦ firstTrajectory A s`, `A ↦ firstPath A`, `A ↦ selectedRows A k`, and `A ↦ pastMatrix k A` are Borel measurable. The exact finite comparison scan and totalized Schur recursion must be used in these proofs.

For the literal `gaussianMatrix n` law and every j:Fin n with k≤j.val, prove the fresh-column identities:

4. `Measure.map (column j) (gaussianMatrix n) = Measure.pi (fun _ : Fin n => gaussianReal 0 1)`.
5. `IndepFun (pastMatrix k) (column j) (gaussianMatrix n)` and thus `IndepFun (fun A => selectedRows A k) (column j) (gaussianMatrix n)`.
6. The explicit joint law is `(gaussianMatrix n).map (fun A => (selectedRows A k, column j A)) = ((gaussianMatrix n).map (fun A => selectedRows A k)).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1))`.

The independence proof will expose the concrete finite independent entry coordinates and disjoint past/current-column coordinate sets (or an equivalent exact product rearrangement). The selected-row result follows by measurable composition with the proved past-matrix factorization. No conditioning on a global successful event is performed. Joint-law integration can then use Fubini in downstream proofs without postulating an adaptive independence premise. The finite-dimensional zero cases are included: a fresh column j cannot exist for n=0, while all deterministic and measurable statements still apply.

All theorem declarations will receive kernel trust and printed-axiom checks. This proposal is for preimplementation review; no proof of the remaining growth bound is claimed.

## Independent preimplementation approvals

Root approved items 1–6 before implementation on 2026-10-06, explicitly confirming the first-k-completed-pivots indexing and absence of global-success conditioning. Root also approved the following whole-block extension before its implementation: define `futureColumns k A : {j : Fin n // k ≤ j.val} → Fin n → ℝ` as the tuple of all original unrevealed columns. Its law is the literal product of standard Gaussian vectors over that finite subtype, it is independent of both `pastMatrix k` and the actual `selectedRows A k`, and the joint pushforward of `(selectedRows A k, futureColumns k A)` is exactly the product of the selectedRows marginal and that Gaussian product. Empty future blocks when k≥n are included. This supplies joint multicolumn freshness, not merely individual column independence, with no added probability penalty.
