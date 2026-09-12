# MI-07 independent statement referee 1 — 2026-09-12

**Verdict: APPROVE the frozen statement boundary for proof implementation, subject to the required second independent statement approval.** This is a statement review, not a completed Lean proof review or a `Lean verified` promotion. No proof implementation was present at this review.

Reviewer: OpenAI Codex agent `solved_statement_inventory`, independent of the MI-07 statement author. I read the complete canonical README and Colbrook manuscript at upstream revision `e7252e5307781a7c897bca6cb124f6ab838f6809`, the actual Definitions and all seven Challenge exports, the complete numerical-target document, and the elaborated definitions. I independently reconstructed the rational witness and reran Lean statement elaboration. I did not author or edit the mathematical boundary or a proof.

## Exact bytes reviewed

| File | SHA256 |
|---|---|
| `NLA/MI07/Definitions.lean` | `369e99eaf3df8a8bbfb214973129ab71fbc95445ba9d176e91d52bca3bc46bc5` |
| `Challenge.lean` | `62fee2804dc12a4ad7edecfa8c1dda2dc39acc2d94475d29805e8e55c3288a59` |
| `NUMERICAL_TARGETS.md` | `70272f54de929a95347db186b09b66d534313eed87ab7daa8e7fe5c8aaa8bd1e` |
| Canonical `MI-07/README.md` at the source revision | `f000dcf3ae8b221bac6f389da7762b37bd439f360b67ff2fd3a4550fc373cf8f` |
| Complete source `MI-07/solution.tex` at the source revision | `de4f6e94c47123d16e28c19cd9bb18010189d66ab0b02c1aad99bf7ca62aaa46` |

I recomputed every source/formalization hash recorded in `statement-freeze.json`; all matched. Lean 4.33.1, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` are pinned. This review does not attest to a fresh Linux dependency rebuild.

## Correspondence to the original question

**Full quantifiers and order.** `TriangleConjecture` says that for every positive dimension and every arbitrary pair of complex square matrices there exist two genuine complex unitaries giving the constant-one domination. It imposes no positivity, reality, rank, self-adjointness or commutativity assumptions on the arbitrary inputs. The fully elaborated comparison uses `Matrix.instPreOrder`, hence `(right-left).PosSemidef`. It is ordinary PSD order, as required, rather than Olson spectral order or pointwise comparison. The two conjugations have exactly the source order `U H U*` and `V H V*`. The unitary subtype ranges over all complex unitaries.

**Actual modulus and powers.** `matrixModulus` calls `CFC.abs`. Its generic bridge requires equality to the actual positive square root of `X*X`, together with PSD. The root sequence uses matrix-ring natural powers: the elaborated terms explicitly use `Matrix.semiring`, not functionwise powers. The outer power explicitly calls `CFC.rpow`. Reindexing the source's positive integer exponent by `r+1` visits every positive exponent and avoids a zero-root or zero reciprocal convention.

**The limit is not an assumed candidate.** `maximalModulus` is the standard `Filter.limUnder` of this exact sequence in the ordinary finite-dimensional matrix topology. It is totalized at inputs lacking a limit. The mandatory `witness_root_limits` export must establish genuine convergence at **each of A, B and A+B**, and `maximalModulus_eq_of_tendsto` must identify each actual limit. Therefore the advertised counterexample cannot exploit a totalized default or an unproved convergence assumption. A proof of convergence for every unrelated complex matrix is unnecessary for this negative answer: the explicit witness, once all these convergence obligations are proved, already refutes the original universally quantified inequality on inputs where its exact canonical limits exist. No global convergence theorem is advertised. The additional generic spectral-norm equivalence binds the finite-dimensional topology to the genuine Euclidean operator norm; elaboration confirms `Matrix.instL2OpNormedRing` in `spectralNorm`.

**Exact witness and obstruction.** The choice `t=5/12` is a member of Colbrook's full positive-parameter family, not a replacement problem. It makes `sqrt(1+t²)=13/12` exactly rational. I independently derived the polar-direction unit vector `(12/13,5/13)`, its projection, the positive-definite spanning sum with first principal entry `313/169` and determinant `25/169`, and all six candidate positive square roots by direct Gram-product checks. The actual CFC identifications and their root-sequence limits remain required Lean conclusions; the finite checks are not hypotheses. The actual limits must have traces `13/6` on the left and `11/6` for every unitary orbit sum on the right. Their difference `-1/3` contradicts the nonnegative real trace of a PSD complex matrix, excluding **every** pair of complex unitaries. There is no optimization or restriction to real orthogonal matrices.

**Complete resolution scope.** The seven exports include generic modulus/limit/norm bridges, finite witness moduli, all three root limits, the all-unitary counterexample, and the full logical negation `not_triangleConjecture`. Proving all seven supplies a complete negative answer to the exact canonical constant-one assertion. The manuscript's stronger no-finite-constant result is correctly excluded; formalizing it is not required to refute the canonical question. The final theorem is not a conditional scalar reduction.

## Independently executed checks

I ran each of these from the project directory; all exited 0:

```
lake env lean NLA/MI07/Definitions.lean
lake env lean Challenge.lean
lake env lean reviews/InspectStatements.lean
python3 reviews/referee-1/numerical_check.py
```

Definitions elaborated without warnings; Challenge emitted precisely its seven intentional `sorry` warnings. These are exclusively statement placeholders, not proof evidence. The independently reproduced elaboration log has SHA256 `de3d4e212d8215221999d0bc8a12f2c928fb7b2b5ede9e912adfcf18cd35e604`, matching the implementer's inspection. Full command records and log hashes are in [referee-1/checks.json](referee-1/checks.json). The independent Fraction checker and its results are in [referee-1/numerical_check.py](referee-1/numerical_check.py) and [referee-1/numerical_check.json](referee-1/numerical_check.json). It uses no floating point and makes no claim to prove CFC identities, convergence or the final universal negation.

## Referee scope and remaining gate

I applied the relevant Tau Ceti correctness, exact scope, proof quality, reuse and attribution criteria to this statement boundary. The use of a rational Pythagorean specialization and a trace obstruction minimizes computation without shrinking the original target. Existing Mathlib CFC, matrix order, unitary and topology APIs are used transparently. Mathematical authorship remains Matthew J. Colbrook; George Stepaniants receives formalization credit with the Department of Computing and Mathematical Sciences, California Institute of Technology. No email is included. This is an independent agent application of those standards, not a run of the Tau Ceti service or external human peer review.

No mathematical statement change is requested. Proof work still requires the second independent statement approval. Final acceptance additionally requires actual proofs of all seven exports, transitive axiom checks allowing only `propext`, `Classical.choice`, `Quot.sound`, two independent proof reviews, and real Comparator/kernel verification. An assumed root-sequence limit, omitted CFC bridge, negative-trace fact without the all-unitary argument, custom axiom, or native-execution trust would not satisfy this approval.
