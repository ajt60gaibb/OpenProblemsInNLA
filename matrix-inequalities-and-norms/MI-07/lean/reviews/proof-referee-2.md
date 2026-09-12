# MI-07 independent final proof referee 2 — PASS

Date: 12 September 2026. Reviewer: OpenAI Codex agent `/root`, independent of the statement/proof implementer `/root/leancert_examples`. **Verdict: approve the complete frozen seven-export proof. No mathematical correction is requested.** This is an independent AI-agent review, not external human peer review or a Linux Comparator result.

I previously read the full canonical target, complete Colbrook solution and numerical plan and independently approved the statement boundary before implementation. For final review I read every line of Definitions, FunctionalCalculus, Proof and Solution and inspected the relevant pinned Mathlib definitions and theorem bodies. I freshly elaborated Definitions, FunctionalCalculus, Proof and Solution into a separate artifact prefix, in dependency order. All four commands exited zero without warnings. All 23 explicit kernel trust checks passed, and every transitive axiom report contains exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Full assertion and seven exports

The formal conjecture retains every positive dimension, arbitrary square complex A,B, and existence of two arbitrary genuine complex unitary matrices, with ordinary PSD domination at the original constant one. It imposes no real, Hermitian, rank or commutation restriction on the universally quantified matrices. A fixed two-dimensional witness legitimately refutes that full universal statement. The stronger informal no-finite-constant theorem is outside this certificate's scope and is not claimed.

The seven exports prove the actual positive-square-root modulus and positivity, identification of a proved actual limit, equivalence with genuine spectral-norm convergence, all finite polar and positivity identities, the three actual root-sequence limits, the all-unitary counterexample and the complete original negation. Solution signatures match the previously approved Challenge boundary at the source level. Actual Linux Comparator is still needed to independently check its exported formal boundary and replay the proof.

`matrixModulus` is `CFC.abs`, definitionally the positive CFC square root of XᴴX. Every inner exponent is a matrix-ring power at the positive integer r+1, and the outer exponent is genuine real `CFC.rpow` at its reciprocal. The PSD order is the Mathlib matrix order, not entrywise or eigenvalue-wise comparison. `spectralNorm` elaborates to `Matrix.instL2OpNormedRing`. I inspected the L2 metric construction: it explicitly preserves the ordinary finite-dimensional topology, so the generic norm-convergence equivalence connects the actual root limits to the correct norm.

## Actual limits, including the singular case

The proof handles the singular projection P correctly. In FunctionalCalculus, `rpow_projection` uses its actual spectrum contained in {0,1}, CFC congruence, and q>0 to prove P^q=P. I inspected the imported projection-spectrum theorem and the real-CFC representation of powers. The zero spectral value remains zero. No unital exponent-zero value or invalid continuity-at-zero argument is used at P.

`rpow_real_smul` follows from genuine CFC composition and real scalar power multiplication on the nonnegative spectrum. The separate `posDef_rpow_tendsto_one` applies continuity at exponent zero only to a positive definite matrix. It uses that matrix's actual positive eigenvalues, actual unitary spectral representation, finite entrywise convergence and continuous unitary conjugation. This is a proved analytic result, not an assumed eigenvalue list or numerical limit.

The concrete finite proofs establish P²=P and Q²=Q, positivity of both, and strict positive definiteness of R=P+Q using its exact nonzero determinant. Each proposed polar factor is independently proved positive and squared to the correct ordered Gram matrix. `CFC.sqrt_unique` then identifies the actual modulus.

These facts give the exact sequences 2^(1/(r+1))P for A, (5/12)I for B, and (13/12)R^(1/(r+1)) for A+B. The reciprocal exponents are positive and tend to zero. The resulting actual limits are respectively P, (5/12)I and (13/12)I. Fresh elaborated inspection confirms that each `maximalModulus` identity invokes its corresponding proved convergence theorem. Although `Filter.limUnder` is totalized outside convergence, the proof uses none of its arbitrary defaults. Generic convergence for unrelated matrices is neither needed nor claimed, and no convergence assumption is added to the original conjecture or final counterexample.

## All-unitary obstruction and numerical trust

I checked the ordinary cyclic trace calculation and the actual unitary star-inverse identity. They prove trace 11/6 for every pair of complex unitary orbit terms, while the left maximal modulus has trace 13/6. Thus right minus left has trace -1/3 for every pair. PSD matrices have nonnegative trace in the genuine complex order, so this is a contradiction for every U,V. No optimization over sampled real rotations replaces the universal unitary quantifier.

The final contradiction visibly retains the LeanCert point certificate 0<1/3. My fresh elaborated inspection contains its actual `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked` proof, its consumer `no_unitary_domination`, and that consumer in the full conjecture negation. Kernel mode is explicit. Exact 2x2 algebra supplies all matrix identities; only a minimal scalar point inequality is checked by LeanCert, without interval subdivision or numerical spectral calculations.

The independent exact rational reconstruction from my statement review remains valid at these unchanged definitions: Q is the outer product of (12/13,5/13), R has first principal entry 313/169 and determinant 25/169, both polar Gram identities hold, and the trace difference is -1/3. Those supplementary checks were not promoted into Lean assumptions. The new full analytic proof discharges the previously outstanding root and limit obligations.

## Proof quality, provenance and evidence

FunctionalCalculus, Proof and Solution contain no holes, custom axioms, unsafe declarations or native decision tactics. They do not import Challenge; its seven intentional theorem holes remain isolated in the comparison template. All ten actual dependency HEADs match the pinned manifest with clean tracked source. My local verification used those dependency artifacts and freshly built this project's modules. It is a macOS development/referee check, not an authoritative Linux sandbox run.

I applied the relevant Tau Ceti correctness/faithfulness, proof-quality, scope, reuse and attribution standards at the pinned rubric revision `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`. The reusable analytic helpers avoid unnecessary numerical work while preserving the original target. Mathematical authorship remains Matthew J. Colbrook. Formalization credit is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI assistance and no George email or external endorsement.

Fresh command records, real outputs, timings, axiom checks, source hashes, elaborated inspection and package checks are retained in [proof-referee-2-root-evidence](proof-referee-2-root-evidence/). The approved numerical reconstruction is retained in [statement-referee-2-evidence](statement-referee-2-evidence/). No mathematical source or canonical status was changed by this referee. Any subsequent mathematical edit reopens the affected review.

- Definitions: `369e99eaf3df8a8bbfb214973129ab71fbc95445ba9d176e91d52bca3bc46bc5`.
- Challenge: `62fee2804dc12a4ad7edecfa8c1dda2dc39acc2d94475d29805e8e55c3288a59`.
- Numerical targets: `70272f54de929a95347db186b09b66d534313eed87ab7daa8e7fe5c8aaa8bd1e`.
- FunctionalCalculus: `0963940bbed1818e7b8240129de01e832660f045dbfcabf578fb11d99949553a`.
- Proof: `55f400e703994c3967a245495f6ad1ebc1999133cfd748185c81ef263178d8a3`.
- Solution: `e460594ac018c8a1e966d88012b07c4ada8743957a414cbdfff8b790d54c07ee`.
- Fresh proof inspection: `799f7cd37c4eda99bd786e22ac0208ecce9413ee428e6c4f9a11f36b37e9a0b6`.
