# MI-21 independent final proof referee 1 — PASS

Date: 12 September 2026. Reviewer: OpenAI Codex agent `/root`, independent of the statement/proof implementer `/root/solved_statement_inventory`. **Verdict: approve the complete frozen proof. No mathematical correction is requested.** This is an independent AI-agent review, not external human peer review or a Linux Comparator result.

I previously reviewed the entire canonical target, Colbrook's source proof, the numerical plan and the three proposed exports before implementation. For this final review I read every line of the completed Proof and Solution, rechecked the unchanged Definitions, and inspected the actual pinned Mathlib definitions and key theorem bodies. I independently compiled Definitions, then Proof, then Solution into a new artifact prefix. All three commands exited zero without warnings. The 11 explicit kernel trust checks passed and every corresponding transitive axiom report contains exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Complete target and actual mathematical objects

The original assertion retains arbitrary positive dimensions and numbers of summands, all positive definite complex input families, all real parameters with t in [0,1], s,r,p>0 and sr≥1, and every unitarily invariant complex matrix norm. The source's order of the noncommuting factors is preserved in both the geometric mean and the aggregate right expression. The actual spectral powers are `CFC.rpow`, and positivity is genuine `Matrix.PosDef` or `Matrix.PosSemidef`.

The chosen `operatorNorm` is the norm of the actual `Matrix.toEuclideanCLM` on complex Euclidean space. Fresh elaborated inspection shows its definitional equality with `Matrix.instL2OpNormedRing`, not a default entrywise norm. I read the `toEuclideanCLM` construction and its vector-action identity, the matrix L2 norm instance, and both CStarRing unitary norm lemmas. The proof establishes all five stated norm properties in every dimension, including full complex homogeneity and invariance under two independently chosen unitary matrices. Thus this norm is an admissible instance of the original quantified class.

The final negation instantiates that full assertion at m=n=2, t=s=1/2, r=2 and p=1, with every premise proved. The public counterexample is stronger in a useful explicit respect: the same witness works for every p>0. The internal right-matrix identity holds for every real p because all its aggregate factors are the identity; the unused positive-p hypothesis in that internal calculation does not weaken the exported assertion or hide vacuity.

## CFC and norm bridges

The generic Riccati lemma identifies a positive semidefinite candidate with the **actual** geometric mean. Positive definiteness of A justifies the inverse-power identities for H=A^(1/2) and J=A^(-1/2). The independently checked A*K=I implies K=A^(-1); real-power addition then gives J²=K. Congruence preserves positivity of J*X*J, and the ordered Riccati equation gives its square J*B*J. Actual `CFC.sqrt_unique`, which I inspected in the pinned source, identifies that root; the proved HJ=JH=I identities finish the original mean formula. There is no assumed root or covariance formula.

The scaled Riccati lemma introduces 1/sqrt(h) with h>0, proves its square is 1/h, applies the preceding actual-mean theorem, and cancels the scalar root only after squaring. It proves both mean evaluations from separately checked rational inverse and Riccati certificates. The four input square roots similarly use genuine positive CFC square-root uniqueness. No approximate matrix root or eigenvalue list enters the proof.

I independently reconstructed the implementation's common-scale certificates with rational arithmetic: h=61697295/8682716, N=[[443355,33000],[33000,605715]]/310097 and N₂=SNS=[[506715,-85800],[-85800,542355]]/310097. The script separately checks N*C⁻¹*N=h*SES and N₂*E⁻¹*N₂=h*SCS, the positive principal minors, both aggregate identities, and (N²+N₂²)/h equal to the frozen witness L. Direct multiplication gives L(1,-4)=(1351000/1350907)(1,-4), with gap 93/1350907>0. This exact check supplements the analytic kernel proof and supplies no assumption to it.

The generic norm lower bound transports the nonzero eigenvector into actual complex Euclidean space, proves the continuous-linear-map eigenvector equation, applies its operator-norm inequality, and cancels only a proved positive vector norm. Thus the eigenvalue is a proved lower bound for the genuine norm. It is not used as a replacement definition of that norm.

## Trust, optimization and review scope

Fresh proof-term inspection contains the actual `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked` certificate for 1<1351000/1350907. Explicit kernel mode is set. The norm lower bound and strict counterexample visibly retain this lemma, and the full negation uses the counterexample. No matrix intervals, parameter subdivisions or numerical eigensolver are needed. Exact rational algebra and reusable analytic lemmas do the remaining work.

Proof and Solution contain no custom axioms, theorem holes, unsafe declarations or native decision tactics, and do not import Challenge. Its three intended theorem placeholders remain confined to the separate, previously approved comparison template. All ten actual dependency HEADs match the manifest with clean tracked source. The independent local build uses those pinned dependency artifacts and a fresh prefix for this project's mathematical modules; it does not claim a fresh Linux dependency build. Actual sandboxed Comparator remains a separate required gate before canonical status promotion.

I applied the relevant correctness/faithfulness, proof-quality, scope, reuse and provenance standards from Tau Ceti's pinned review rubrics (`afb424eda89e8ac96d9eb69f6a88972055a4cd1b`) within the unchanged NLA target. The work credits Matthew J. Colbrook for the mathematics and George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, for formalization with AI assistance. No George email, source-author endorsement or unrelated strengthening is claimed.

## Bound evidence

Fresh commands, exit codes, timings, logs, source identities, proof inspection and actual package checks are retained in [proof-referee-1-root-evidence](proof-referee-1-root-evidence/). The independent rational reconstruction source is there as well. The mathematical hashes are bound by `source-identity.json`, which confirms that the reviewed files did not change during compilation. Any mathematical edit reopens the affected review.

- Definitions: `18ebd6d65063b6e970d76b60aab6a8a8bc595189e9b8e188895030d2172f1055`.
- Challenge: `f7dd628a7635e8860dec64460bd53adfa71ca391eec763391ae1c8e58d1588b4`.
- Numerical targets: `4b0582a3c2da02abf7a349e4ab4af682f6b29bf7026bff21d53edff3ab216312`.
- Proof: `7db067a9cc73e3cda027e2e01d664e4b12bf5af84e8f6b3bb10d9bd4de30e9bc`.
- Solution: `a30f8dfd1103b6ba1f1aca927e7ef4a92b6fa8ae70658463cdea649378ae1a50`.
- Fresh proof inspection: `ba44e111be7477e49bdc89b2f0610854e37ba0ffca16e2e9d3c54ae345ce0a71`.
