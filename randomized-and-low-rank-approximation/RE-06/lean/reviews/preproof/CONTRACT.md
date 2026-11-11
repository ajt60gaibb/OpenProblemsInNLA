# RE-06 frozen pre-proof contract

Status: packet author draft ready for two independent non-author pre-proof reviews. No mathematical RE-06 proof implementation is authorized by this packet. The author is `/root/proof_route` in the multi-agent campaign. This is not an independent review or a verified-problem promotion.

The immutable published base is `099805ef1ce7347d373e47cccc3b2d7cf580a99e`. `INPUT_LOCK.json` binds 49 published files, including the complete canonical problem and Sidney Holden solution in TeX/PDF, retained submitted manuscript and review archive, full statement specification and four existing boundary/specification reviews, the five local Lean source dependencies, toolchain/package pins, permanent registry, and AGENTS instructions. The author read the complete canonical solution TeX and extracted 12-page PDF, and visually inspected its rendered title/author page. Supplementary SVD reuse is separately bound by `REUSE_LOCK.json`; it does not alter this published source base.

The permanent ID is **RE-06**, at `randomized-and-low-rank-approximation/RE-06/README.md`. All 217 published ID/path pairs and all original source bytes remain unchanged. Sidney Holden retains mathematical authorship of the affirmative manuscript. Subsequent Lean implementation must separately identify formalization authors and source reuse.

The final exports must have these literal types in namespace `NLA.Proofs.RE06`:

```lean
theorem svd_total  :
    NLA.Computation.NonadaptiveMatrixQuery.SVDTotal

theorem query_bound (n m : ℕ) (hn : 0 < n) (ε : ℝ) (hε0 : 0 < ε) (hεh : ε < 1 / 2) :
    NLA.Computation.NonadaptiveMatrixQuery.QueryBound n m ε 4000000 0

theorem successful (n m : ℕ) (hn : 0 < n)
    (F : NLA.Computation.NonadaptiveMatrixQuery.Family n m) (hF : Function.Injective F)
    (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hε0 : 0 < ε) (hεh : ε < 1 / 2) :
    NLA.Computation.NonadaptiveMatrixQuery.Successful F A ε

theorem original_claim  :
    NLA.Statements.RE06.OriginalClaim

theorem explicit_claim  :
    NLA.Statements.RE06.ExplicitClaim

theorem target  :
    NLA.Statements.RE06.Target

```

`Challenge.lean` is the mechanically elaborated signature source. Its six `sorry` bodies are intentional negative tests, not candidate proofs. Each is rejected by `#assert_trust kernel`. The final implementation must replace every body with a kernel proof and pass the same exact declarations, without importing Challenge or using its holes.

The closed target is exactly the published

```lean
NLA.Statements.RE06.Target =
  (NLA.Computation.NonadaptiveMatrixQuery.SVDTotal ∧
   NLA.Statements.RE06.OriginalClaim ∧
   NLA.Statements.RE06.ExplicitClaim)
```

The identity above describes the actual reducible definition; scaffold `live_frozen_identity` independently elaborates equality to the retained `NLA.ReviewedStatements.RE06.Target` by `rfl`. A statement identity is not a proof of either proposition.

`OriginalClaim` chooses one absolute real `C > 0` and one natural exponent `b` before **all** `n,m,F,A,ε`. For every positive dimension, injective family enumeration `Fin (m+2) → Matrix (Fin n) (Fin n) ℝ`, arbitrary target matrix and `0 < ε < 1/2`, it requires both the exact query bound and success of the one frozen program. `ExplicitClaim` fixes `C=4000000`, `b=0`. Thus it is enough to prove `query_bound` and `successful` uniformly, then assemble both named claims with `C=4000000,b=0`; their full literal exports remain required. `svd_total` is a proved affirmative fact for **every** rectangular real matrix, including zero dimensions; it may not be added as a premise of success.

The program is frozen in `NLA.Computation.NonadaptiveMatrixQuery`. `makePlan n m ε ω` receives no matrix, family member selection or oracle response. It commits either all standard-basis right queries or disjoint standard-Gaussian right/right/left blocks. `oracleAnswers` evaluates that entire finite list; `postprocess` receives only the plan, known family and stored responses. It makes no extra query. Each right or left call counts one, including repeated or zero vectors. The exact declared `QueryBound` quantifies **every** stream `ω`; its right side is `C * sqrt(log(2*(m+2))) * ε⁻¹^2` times the declared logarithmic bracket to power `b`. For the required `b=0`, the bracket is exactly one.

The probability is the original `GaussianLaw = Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)` on the actual countable stream, not a replacement independent probability model without a proved transport. For each fixed input, `Successful` is the literal event that the actual `run` returns a family member whose Frobenius error is at most `(3+ε)` times the attained finite-family optimum, with measure at least `99/100`.

No conditioning, positive-optimum, full-rank, gap, bounded-norm, large-dimension or generic-position assumption may enter a public theorem. Rank-deficient and zero sketches have their actual defined pseudoinverse output. If `OPT=0`, success requires exact output `A`. Exceptional sets may be proved null internally, not deleted from the domain or hidden in a new law. The full-recovery branch must be proved for its actual finite transcript. The SVD primitive is the actual `exactSVD`, with validity and the SVD-defined pseudoinverse connected to any alternative formula used in analysis. No arbitrary output/cost oracle, conditional-success-only query count or weaker error objective is acceptable.

Implementation must use pinned Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, with `leancert.trust "kernel"`, theorem trust assertions and axiom inspection. Final proof closure must contain no sorry/admit, custom axiom, unsafe proof or native decision shortcut. Only the standard kernel axioms `propext`, `Classical.choice`, `Quot.sound` are admissible. Standard classical choice in the retained exact-real model is not evidence of a measurable SVD selection; that bridge must be proved when needed.

Before any RE-06 proof implementation, two independent non-author reviewers must approve the **same** `INPUT_LOCK.json`, `REUSE_LOCK.json`, `Challenge.lean`, `EXPORTS.json`, `CONTRACT.md` and `READINESS.md` hashes and inspect the original target/operational semantics. Historical 2026-10-09 statement reviews and TR-04 SVD approval do not satisfy this new gate. Changes to a reviewed signature or actual semantic input require renewed review of the changed bytes. No proof or support result, author scaffold replay, source archive or numerical experiment is itself a review approval.

After implementation, separate independent statement/proof/package reviews, a fresh pinned Lean closure replay, all six exact statement comparisons with empty Comparator definition allowances, standard-axiom checks, and actual authoritative Linux CI receipts are required before claiming full verification. None of those final results is claimed here.
