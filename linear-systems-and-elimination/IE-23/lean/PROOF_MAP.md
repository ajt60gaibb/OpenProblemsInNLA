# IE-23 completed proof correspondence

This describes the implementation of the eight independently approved
contracts. The original `NUMERICAL_TARGETS.md`, `SOURCE_CORRESPONDENCE.md`, and
statement-stage README remain the immutable pre-proof plan. The final raw
checks and exact identities are recorded separately in `verification/` and
`reviews/proof-completion.md`; two independent final proof reviews and an
actual Linux execution are later gates.

The mathematical resolution remains Matthew J. Colbrook's. The rational
example retains Dokmanić–Gribonval's attribution. George Stepaniants is the
AI-assisted formalization author, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
No contact email or new mathematical priority is claimed.

| Frozen export | Completed proof and actual semantic bridge |
| --- | --- |
| `inducedNorm_semantics` | `Norms.lean` proves coordinate modulus ≤ the actual finite-real-p norm, Euclidean norm ≤ the sum of coordinate moduli, and then the finite matrix-entry sum bound. It supplies nonempty and bounded ratio sets, genuine `isLUB_csSup`, nonnegativity and the all-input bound, including zero input. It applies to every original finite real p>2 and all original dimensions, with no extra boundedness assumption. |
| `witness_matrix_identities` | `Matrices.lean` proves the exact products for A, B, X, G and Ginv. It builds a genuine unit from both inverse equations and uses `Matrix.inv_eq_left_inv` for the actual inverse. Actual rank follows from AX=I, rank-of-product monotonicity and the rank-height bound. The genuine pseudoinverse definition is then evaluated. |
| `fourth_power_norm_control` | `FourthPower.lean` proves the actual positive fourth-root and real-power identities. It uses `EuclideanSpace.norm_sq_eq` and `Real.rpow_inv_natCast_pow` to connect the norms to their exact powers. The sole universal scalar comparison is the sum-of-squares identity `(a²−b²)²≥0`, followed by two justified nonnegative-square comparisons. |
| `witness_action_identities` | `Actions.lean` proves actual matrix-vector products for arbitrary complex y. Exact real/imaginary expansion proves the B identity and X isometry. For every complex right inverse Y, the actual equation AY=I forces Yz=(t,1−t,−1−t), from which the squared Euclidean norm is exactly 2+3|t|². No competitor parameterization is assumed. |
| `witness_attainment` | `Actions.lean` proves z≠0 and its actual finite-p denominator and Euclidean numerators. Positivity of the genuine fourth root justifies both divisions, so both ratios attain c=√(√2). |
| `witness_norms` | `Minimizers.lean` applies the universal upper bound using `csSup_le`, and the actual nonzero witness ratio using `le_csSup`. Both suprema equal c; an empty or unbounded supremum default plays no role. |
| `witness_global_minimizers` | The all-competitor action gives the actual unsquared norm lower bound √2 at z. This ratio bounds every competing supremum below by c. Both exact feasible matrices attain it, proving two global minimizers and an actual least feasible value. |
| `not_rightInverseUniqueConjecture` | The full original universal predicate is instantiated at m=2, n=3, p=4 and the exact full-row-rank A. X is a genuine right inverse distinct from the actual pseudoinverse B. Its asserted strict inequality contradicts the two equal supremum values. |

`Proof.lean` assembles these conclusions into the eight internal contracts;
`Solution.lean` exports exactly the frozen Challenge signatures. The completed
proof imports no Challenge object. LeanCert explicitly audits kernel trust for
both the internal and public contracts; only the three standard axioms are
permitted. There is no approximate arithmetic, interval subdivision, numerical
eigenvalue computation, or external certificate oracle.

The full negative canonical answer is proved. The manuscript's stronger all-p
families, complete minimizer classification, endpoint results and separate
product-norm objective remain outside the eight formal exports, as specified
and reviewed before implementation.

For a normal checkout with its own dependencies, the explicit proof build is
`lake build Solution`; the deliberately frozen default target remains
Challenge. Under the current disk constraint, the recorded author and referee
checks use the exact pinned MI-22 dependency objects **read-only**, fresh IE-23
project object prefixes and the real Lean 4.33.1 executable. That is a full
fresh re-elaboration of this proof's modules, not a local Lake invocation,
dependency-source rebuild, or Linux Comparator run.
