# MI-07 completed local proof handoff

Status: complete local kernel proof, ready for two independent final proof referees. Linux Comparator and publication remain root-controlled pending stages. No canonical page, status, commit, push, or public PR was changed by this implementation.

The two statement approvals were read before proof implementation. `Definitions.lean`, `Challenge.lean`, and `NUMERICAL_TARGETS.md` remain byte-identical to their approved statement freeze. `proof-freeze.json` binds the mathematical files, approvals, and raw evidence.

## Exact scope and seven exports

The proof refutes the complete original universal constant-one assertion over arbitrary complex matrices and arbitrary complex unitary witnesses. It specializes Colbrook's published counterexample family to t = 5/12, while retaining the original CFC modulus, positive integer root sequence, actual topological limit, ordinary PSD order, and actual spectral norm. It does not claim the source's stronger no-finite-constant theorem or generic convergence for every matrix.

The seven exports prove: (1) the genuine positive square root modulus, (2) identification of the actual limit from proved convergence, (3) equivalence with convergence in the Euclidean operator norm, (4) all exact finite polar and positivity identities, (5) all three actual root limits, (6) the exact witness and trace obstruction for every complex unitary pair, and (7) the original conjecture's full negation.

## Analytic bridges and computation scope

`FunctionalCalculus.lean` supplies three proved helpers. A positive CFC power of a PSD projection retains its nullspace via the actual projection spectrum {0,1}. Positive real scaling of a CFC power follows from genuine CFC composition and real scalar powers. CFC powers of a positive definite matrix converge to the identity as the exponent tends to zero, by its actual positive eigenvalues, actual spectral representation, and finite entrywise topology.

The actual sequences are proved exactly:

- A: 2^(1/(r+1)) P, tending to P. No exponent-zero unital value is substituted at the singular projection.
- B: (5/12) I for every index r.
- A+B: (13/12) R^(1/(r+1)), tending to (13/12) I because R=P+Q is positive definite.

The generic spectral-norm bridge uses Mathlib's L2 operator norm instance. Every invocation of `Filter.limUnder` is identified from a proved convergence theorem; no totalized-limit default is used to create the witness.

The only LeanCert numerical task is the rational point inequality 0 < 1/3, with explicit `trust := kernel`. Its checked dyadic interval is the degenerate point [0,0]; there is no matrix interval calculation or nontrivial interval subdivision. Exact 2x2 arithmetic proves the finite identities and trace gap. `proof-certificates.log` shows the retained checked LeanCert proof and the explicit use of `scalar_gap_positive` in `no_unitary_domination`, which is used by the final negation.

## Validation

`lake build Solution` passed with 3149 jobs, no warnings or errors. Raw output and actual exit status/timing are in `proof-build.log` and `proof-build-result.json`. All 23 explicit kernel trust assertions passed. The 23 corresponding transitive axiom reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`; see `proof-axioms.log`. Source scanning found no proof holes, admissions, custom axioms, or native decision trust in `Proof.lean`, `FunctionalCalculus.lean`, or `Solution.lean`.

Direct elaboration of `InspectProof.lean` and `InspectCertificates.lean` passed. Their retained logs show the exact signatures, actual CFC bridges, all-unitary scope, full negation, and checked certificate usage. Seven intentional placeholders remain only in the separate Comparator challenge, which Solution does not import.

Formalization author: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. Mathematical counterexample attribution remains Matthew J. Colbrook. No email is included.

## Frozen mathematical hashes

- `NLA/MI07/Definitions.lean`: `369e99eaf3df8a8bbfb214973129ab71fbc95445ba9d176e91d52bca3bc46bc5` (3041 bytes).
- `Challenge.lean`: `62fee2804dc12a4ad7edecfa8c1dda2dc39acc2d94475d29805e8e55c3288a59` (3314 bytes).
- `NUMERICAL_TARGETS.md`: `70272f54de929a95347db186b09b66d534313eed87ab7daa8e7fe5c8aaa8bd1e` (11543 bytes).
- `NLA/MI07/FunctionalCalculus.lean`: `0963940bbed1818e7b8240129de01e832660f045dbfcabf578fb11d99949553a` (3842 bytes).
- `NLA/MI07/Proof.lean`: `55f400e703994c3967a245495f6ad1ebc1999133cfd748185c81ef263178d8a3` (16035 bytes).
- `Solution.lean`: `e460594ac018c8a1e966d88012b07c4ada8743957a414cbdfff8b790d54c07ee` (4443 bytes).
