# Independent review before selected-block elimination implementation

Reviewer: /root/independent_math_review. The coordinator's exact specification
in selected-block-elimination-specification.md is approved before coding.
For nonsingular A the actual canonical path has nonzero pivots. The selected
original row labels in their pivot order produce a block T whose no-pivot
upper factor has exactly these nonzero pivots; its rows are linear combinations
of T's rows, so its nonzero determinant forces det(T)≠0. This also covers t=0.

On coordinates of all unselected original labels, an active elimination row
has exactly its original identity coordinate. This follows under the actual
swaps because each pivot is removed from the unselected set and its row has
zero coordinates on the later remaining labels. The active original label is
outside the selected prefix since rowLabels is a permutation. Exact annihilation
of the first t original columns therefore gives c*T=-z for the selected-row
coefficient vector c; multiplying by T⁻¹ yields c=-z*T⁻¹. This proves the stated
coordinate identity with the indicated minus sign and row-vector order.
The identity coordinate and selected-label coordinates are disjoint, and the
selected-label embedding is injective, hence the row's squared Euclidean norm
is exactly 1+sum_a((z*T⁻¹)_a)^2. There are no hidden row permutations, independence
assumptions, or claims of measurable singular-vector choices. The coordinator
will independently review the implemented proofs.

Before the prefix extension was implemented, the coordinator additionally
approved the stronger exact premise: only the first t actual canonical pivots
are nonzero. This is independently approved: the remaining-coordinate identity
needs only active pivot indices, and annihilation of the first t columns uses
only these t nonzero pivots. The resulting selected-block nonsingularity,
coordinate identity and square-norm formula therefore hold under PrefixNonzero
ht A, defined literally by those t actual firstTrajectory entries. Full A
nonsingularity is retained as a corollary via canonical admissibility. This
extension introduces no event conditioning or stochastic premise.

Completed code: `NLA/IE06/SelectedBlockElimination.lean`, SHA-256
`8878c320c99fda38e3ef5e6268071238b5f5e65579cb2a902e049e3e43cd3eca`.
All 18 local declarations passed their individual LeanCert kernel-policy
assertions; the printed transitive axioms contain only propext,
Classical.choice, and Quot.sound. No compile warnings remain. The private
pinned-runtime build used already compiled imports (including read-only copies
of the author's frozen F7 closure); receipt/log are in
`reviews/selected-block-elimination/`. This does not claim a fresh rebuild or
kernel replay of cached dependencies. The coordinator will independently
review the frozen source. The exposed prefix bridge includes Good(T) and
full nonsingularity corollaries; no random singular-vector choice appears.
