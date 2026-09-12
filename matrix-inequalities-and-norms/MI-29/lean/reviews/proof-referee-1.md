# MI-29 independent final proof referee 1

Date: 2026-09-12. Reviewer: OpenAI Codex AI agent `/root`, who did not author the MI-29 definitions or proof. **Verdict: approve the complete negative formalization of the original target.** This is an independent AI-agent proof review, not external human peer review. Linux Comparator verification and publication metadata remain required.

## Target and analytic semantics

The earlier independent statement review read the complete canonical README, solution TeX and Markdown, and pinned Mathlib definitions. For this final review I read every line of the frozen Definitions, Challenge, completed Proof and Solution. The exact original assertion still quantifies every positive dimension, positive definite complex matrix A, invertible Hermitian complex matrix B, and arbitrary nonnegative real exponents k,p. The inequality remains the original right determinant at most the left determinant. No positive-definiteness restriction on B, integer-only exponent restriction, commutation, assumed spectrum or extra numerical premise has been introduced.

The counterexample proves all its own hypotheses. Instantiating the full assertion at n=3,k=6,p=8 and the concrete A,B immediately contradicts the proved strict reverse inequality. Thus the final negation resolves the complete canonical yes/no target. The source's separate semidefinite extension, established k=2 case and B>0 variant are outside this certificate.

`spectralPower` is the actual unital `CFC.rpow`, not the competing pointwise power of a matrix represented as a function. The generic natural-power bridge directly uses the positive-semidefinite premise of `CFC.rpow_natCast`, including exponent zero. `matrixModulus` is actual `CFC.abs`, definitionally the positive CFC square root of XᴴX. The proof derives positivity from `CFC.abs_nonneg`, applies the genuine identity `CFC.abs_sq`, and reduces the actual eighth power to the fourth power of the Gram matrix. Nothing about the analytic square root is assumed as a witness certificate.

The generic positive-real determinant theorem proves more than is needed for the final witness: positive definiteness of A is preserved by every real CFC power, and the other summand is positive semidefinite. Both sums are therefore positive definite and both determinants are strictly positive real complex numbers. This handles zero exponents as well. Some original hypotheses can be unused in this supporting theorem because the proof is stronger; they have not been removed from or replaced in the universal target. The inspected complex order requires equal imaginary parts and compares real parts, so the advertised real determinant comparison is justified independently and is not exploiting undefined ordering.

## Exact counterexample and computation

A is the actual diagonal matrix diag(2,1,1/2); positive definiteness is established entry by entry. B is the symmetric integer witness divided by five. Its exact determinant −1/125, together with the matrix determinant criterion, proves actual ring invertibility. The negative diagonal of B and a negative diagonal of −B separately contradict positive semidefiniteness, so the optional indefinite witness properties are also proved.

The two noncommuting Gram identities are in the correct order: (AB)ᴴ(AB)=BA²B and (BA)ᴴ(BA)=AB²A. They follow from genuine conjugate-transpose multiplication and the proved Hermitian properties. The CFC reductions are applied before any rational matrix arithmetic. Each named finite matrix is a private proof aid whose equality to the actual product, square or sum is then proved by exhaustive entrywise rational normalization. The final determinant evaluations use the true three-dimensional determinant formula. These are consequences of the definitions, not assumed tables.

The exact determinants are 136990346414301954149/61035156250000000000 and 4537743716162890657/1907348632812500000. Subtraction gives the positive right-minus-left gap 21036678407451/156250000000000. My earlier independent `Fraction` reconstruction of the actual ordered matrix products and signed determinant expansion produced these same values; those records remain bound to the unchanged statement inputs. This final review checked each additional intermediate matrix certificate and its Lean equality proof in the complete source. Referee 2 additionally reconstructed every intermediate certificate independently.

Only one scalar positivity comparison is sent to explicit kernel-mode LeanCert. It is used by `witness_strict_violation`, then the complete witness and universal negation, so the numerical certification is substantive. The proof avoids interval subdivision, approximate eigenvalues, numerical square roots and expensive eighth-power expansion. The actual modulus is reduced analytically; two repeated squarings and the exact 3×3 determinant suffice. Importing the small LeanCert point-inequality module further reduces the dependency build without changing the statement or trust mode.

## Independent re-elaboration and trust

I independently re-elaborated Definitions and Proof into a separate local directory, then re-elaborated Solution with those freshly built artifacts first in the import path. All three actual commands exited zero. The ten internal and five public axiom reports contain exactly `propext`, `Classical.choice` and `Quot.sound`; all fifteen explicit kernel trust assertions passed. [Raw command records and logs](../verification/referee-1/) record this macOS run and its hashes. It is not an authoritative Linux Comparator run.

No sorry, custom axiom, unsafe proof shortcut, extra trust in native evaluation, hidden hypothesis or Challenge import was found in the Solution dependency chain. The five intended Challenge placeholders remain isolated. The public signatures match the frozen Challenge by source inspection; Linux Comparator must still verify mechanical identity and kernel acceptance with no definition holes. All source and pin bytes in the proof freeze remained unchanged after this review.

Relevant Tau Ceti correctness, fidelity, scope, quality, generality, reuse, API, naming, placement, documentation and attribution angles were applied within this project's scope. The proof uses Mathlib's actual matrix order, CFC, determinant and invertibility interfaces. Generic analytic bridges are reusable and separately exported; private numerical certificates remain implementation aids. The full original target is settled by a concrete admissible witness, while stronger variants are explicitly excluded.

George Stepaniants is credited for formalization with the Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA affiliation. Matthew J. Colbrook retains mathematical authorship. AI-agent assistance and reviews are disclosed, without publishing George's email or claiming human endorsement.

## Bound bytes

| Input | SHA256 |
|---|---|
| `NLA/MI29/Definitions.lean` | `c73bfb1856b3e1059ce2ef1e35f8314cb339edcc38b89d28780d38b122ce1a16` |
| `Challenge.lean` | `7ac10b3c284dc5f86dbbb90ef999d5b210540dd0fbdc0bfc60ee9621d25da3cf` |
| `NUMERICAL_TARGETS.md` | `892449f4f9107661242eca72c50d4f35652a4475ea94573daf2ad865c44e5af2` |
| `NLA/MI29/Proof.lean` | `b683a2c0faebd595f7d9f2b0973a9955cf39443c924f7dfd05b3b60e16bdadf5` |
| `Solution.lean` | `0cb66f4fc4d379f1f91699ba16b6feda93710798fe414fa09b242cd12076ce11` |
| `verification/referee-1/proof.log` | `58ae718c74509f56ebadd51d69085cff219f55c83c4c7582984e04f727106357` |
| `verification/referee-1/solution.log` | `9422b8d591abb90fa71f1cce3adf6773f238b67874b8291d4a4712da3c712a40` |

Mathematical changes reopen the affected statement/proof gates. Final metadata must preserve this complete negative scope and accurately distinguish local review from the still-required Linux check.
