# AV-02 implementation correspondence

Author of this implementation and specification: OpenAI Codex AI agent
/root/statement_design, 2026-09-28. Before implementation, the final
specification hash
26dba9081ffffa9d4b46d2feee2749992fb659bc2e9d12afdaeabb0a672da7da
was checked against independent /root and /root/inventory approvals.
Both independent final reviews of the shared oracle/NP model were also
verified against all bound bytes. No metadata or canonical source was changed.

InDiagonalCube is the complete real closed cube [-1,1]^n with weak endpoint
inequalities. Perturbed embeds every rational entry of A exactly into a real
matrix and subtracts the actual diagonal matrix of d. Regular requires the
determinant to be nonzero for every real d in that cube. InputPromise retains
n>=1, a positive rational threshold and this full regularity condition. No
triangular, symmetric, diagonal-2, generic or finitely sampled restriction is
introduced, and off-diagonal entries do not vary.

SpectralNorm is the norm of LinearMap.toContinuousLinearMap applied to the
actual Matrix.toEuclideanLin map. The pinned toEuclideanLin is toLpLin 2 2,
so this is the real Euclidean induced operator norm, not an entrywise or
Frobenius norm. The continuous map retains exactly the same linear action.

ConditionNumber is the actual real sSup over norms of inverses throughout
the entire cube. On a promised input the cube is nonempty and compact, every
perturbed matrix is invertible, and inversion is continuous there. Its norm
therefore has a finite attained maximum. Hence this real sSup equals the
canonical maximum, with no empty/unbounded-supremum convention involved.
Regularity also ensures the imported total matrix inverse is the genuine
inverse at every point used. These are mathematical correspondence facts;
no compactness or continuity theorem is assumed as a free target premise.

LegalWords is exactly the fixed binary encoding of a ThresholdInput satisfying
InputPromise. YesWords uses the same encoding and promise, with the exact
non-strict comparison threshold<=ConditionNumber. Equality remains a yes
instance. Both languages are concrete definitions; a caller cannot substitute
a favorable interpretation. All dimension, matrix and threshold bits appear in
the dense fixed encoder. The canonical grammar is unique as checked in the
shared source review; no alternative encoding or analytic promise-recognition
algorithm is postulated.

Target is the shared concrete Complexity.OracleNPHard of those two fixed
languages. Its full expansion quantifies every binary language in the concrete
finite-verifier NP class; then one finite three-tape oracle machine and one
uniform polynomial bound; then every oracle correct on all legal target words;
then every input word. The one successful bounded run must return its exact
Boolean answer and every actual recorded query in that run must be legal.
The runtime counts actual finite-tape transitions and query actions under the
reviewed semantics. Malformed query failure and successful halt are distinct,
and off-promise oracle answers are unrestricted. No favorable-oracle choice,
free MAX-CUT solver, reduction map with assumed cost or unit-cost spectral
routine enters the statement.

This is the requested promise-preserving polynomial Turing NP-hardness
proposition. It is not weakened to a numerical MAX-CUT equivalence or replaced
by the stronger restricted many-one/NP-completeness theorem. The original
source credit and resolved mathematical status remain unchanged.

The module selects LeanCert kernel trust and runs #assert_statement,
#assert_trust kernel and #print axioms on the safe closed Target definition.
Final pinned Lean 4.33.1 local macOS compilation passed with only propext,
Classical.choice and Quot.sound. Author-local receipts and logs are at
/private/tmp/nla-av02-evidence, and builds at /private/tmp/nla-av02-build.
An initial matrix/function elaboration ambiguity was resolved by the explicit
Matrix.of constructor before the successful build; no mathematical target
change was needed.

The shared machine/encoding/NP/oracle modules and all dependency pins must be
bound in the final independent source reviews. General codec/simulation
theorems, MAX-CUT completeness, an implemented reduction and its cost/gap
proofs remain separate future proof obligations. No target theorem or Linux
Comparator pass is claimed merely by this statement's elaboration.
