# IE-10 implementation correspondence

Author: OpenAI Codex AI agent /root/statement_design, 2026-09-28.
Independent preimplementation approvals by /root and /root/inventory were
checked against the final specification hash
eec19ed42d3b851c634f3d775533002b4f9499a0e00f1ccd2a6d312e40529e7d
before writing this implementation. The live source defines the full Target
proposition and supplies no proof of its probability inequality.

GaussianLaw is the actual finite product of the pinned gaussianReal 0 1,
with one coordinate for every Fin n times Fin 2. That API takes mean and
variance. ComplexGaussian uses the two real coordinates as real and imaginary
parts; Start normalizes their full Euclidean norm, with e_0 on the zero draw.
The variance-two convention for this complex Gaussian has a common scale that
cancels in normalization. For n>=3 this is the original complex sphere law.
There is no separate random subspace or basis distribution.

VectorNorm is the square root of the sum of squared complex coordinate norms.
Inner conjugates the first argument. CyclicShift has its one in row j+1 mod n
of column j. Krylov uses the actual nonnegative matrix power followed by
ordinary matrix-vector multiplication.

GramSchmidt is a structural natural recursion storing the preceding normalized
residual vectors in their original order. Residual subtracts the projection
against each stored vector; its finite list sum contains exactly the prior
columns. Column is the next normalized residual of precisely C^j b. Normalize
assigns zero at a failed residual. Basis uses Column directly, so no out-of-range
list indexing or default vector enters a successful compression. FullRank
requires every residual at j<k to have positive Euclidean norm. Compression is
the actual conjugate-transpose product Q* C Q. All finite k are defined; only
2<=k<n with n>=3 occurs in Target.

The pinned Matrix.toEuclideanLin is toLpLin 2 2 between complex Euclidean spaces.
The pinned LinearMap.toContinuousLinearMap in
Mathlib/Topology/Algebra/Module/FiniteDimension.lean is the canonical continuous
extension of a finite-dimensional linear map, preserving its values.
SpectralNorm applies the actual continuous-linear-map operator norm to that map.
It is not the function-space entrywise norm or the Frobenius norm.

EigenvectorCondition takes sInf in ENNReal over all exact diagonalizations
H=V*diagonal(d)*V inverse, with nonzero determinant explicitly required. Over
Complex the imported total matrix inverse is the genuine inverse under that
guard. The set records ofReal(||V||_2*||V inverse||_2), a nonnegative value.
The empty ENNReal infimum is top, so a nondiagonalizable matrix has the stipulated
infinite condition number. No diagonalizer is selected and no attainment of the
infimum is presumed. Repeated eigenvalues, reorderings and arbitrary complex
column rescalings all remain in the quantified set.

CompressionCondition assigns top when any Krylov residual fails. Since the
threshold is the ofReal image of a finite real expression, these failures
cannot count as successful. The approved specification explains the almost-sure
full-rank and unitary-basis-invariance correspondence in this precise cyclic
sphere model. These facts are not passed into Target as axioms or assumptions.

Target chooses one positive real C and one positive real c before every allowed
n,k. The threshold uses ordinary positive-base real power, C*(n:Real)^c.
The exact success probability is at least ofReal(99/100), and the success event
uses a non-strict extended condition-number comparison. No expectation theorem,
chosen numerical constants or simultaneous-in-k guarantee replaces the original
existential-constant target.

The module explicitly sets LeanCert trust to kernel and runs #assert_statement,
#assert_trust kernel and #print axioms on the closed safe Target definition.
The final source compiled with pinned Lean 4.33.1 and the campaign's exact
Mathlib/LeanCert dependencies. The only reported axioms are propext,
Classical.choice and Quot.sound. Author-local evidence is retained at
/private/tmp/nla-ie10-evidence, with build outputs in /private/tmp/nla-ie10-build.
The first compile exposed a missing ENNReal notation scope, corrected before the
successful final compilation; no target change was needed.

No probability, measurability, Gram-Schmidt correctness, model correspondence
or catalog target theorem is claimed proved here. Those are later mathematical
proof obligations; the source provides concrete definitions sufficient for the
statement. Final independent reviews must inspect these actual definitions,
the frozen copy, their complete local import closure and the pinned external
meanings. Linux CI and Comparator identity checks remain separate verification
gates. No numerical computation is needed merely to state this proposition.


The concrete helper definitions reside in the shared
NLA/Statements/KrylovCompression.lean module. The first frozen identity check
exposed that two separately elaborated recursive GramSchmidt definitions did
not reduce definitionally across namespaces. All helper bodies were moved
unchanged to this shared module; the exact Target expression is unchanged and
both boundaries now import the very same helpers. This structural correction
preserves every mathematical definition and keeps the shared file in the final
review import closure. Actual fresh compilation of live, frozen and a
Target-equality-by-rfl theorem is required; textual similarity alone is not the
identity gate.

The corrected shared-helper layout passed fresh live and frozen compilation and the actual rfl identity theorem checkIE10, all exit zero with only the standard three axioms. Exact author-local identity receipts are in /private/tmp/nla-ie10-evidence/identity-result.json and CheckKrylov.log.
