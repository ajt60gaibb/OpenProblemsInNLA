# MI-03 independent final proof referee 1

**Verdict: APPROVE the frozen mathematical implementation for the next verification gate.** I found no mathematical correction to request. This is an independent AI review by `/root/formal_review_standards`, which did not author the statements or proof. I previously reviewed the statements independently. The author `/root` does not count as a referee. The approval is specific to the hashes below; it is not a claim of external human review, official Tau Ceti endorsement, or successful Linux Comparator execution.

The complete original odd-summand conjecture is proved. The implementation establishes the stronger sharp constant `k / 4` for every `k ≥ 2`, all positive dimensions, and every tuple of complex contractions in the actual Euclidean operator norm. Both attainment and the lower bound on every admissible constant precede the ordinary real-infimum equality. No literature upper bound, matrix-root formula, phase data, or sharpness certificate is supplied as an assumption.

## Reviewed bytes and reproducible checks

The proof freeze is `fcff9e256a6425853b15def24260b419613a72d9122c0a5bedea4b4cd5f0fd1d`, containing 101 project inputs and eight unchanged original sources at `c0601d8825e9f9e744212c62e6a43fefc1c60a22`. The completion note is `919751e1f0595efd095250f2a6b2690b3214c96d988665fb7404d30690f2a729`. All 27 approved statement inputs, both statement reports, and the recorded proof-start gate remain intact. My checks compare each original source both with its recorded SHA-256 and its actual Git blob. The original source TeX, canonical statement, source review, numerical targets, source map, complete definitions, and all implementation modules were read.

| Input | SHA-256 |
| --- | --- |
| `Definitions.lean` | `12f5c9c25dc68e0032679b76cb9d328279ce803b4de437db8e1a564c499c7de6` |
| `Challenge.lean` | `6d7905413c8234a816c79287e58eddcf0ff6267c043336392744c3e30b68fb34` |
| `Modulus.lean` | `170c030ba5a308c385e2a187932433208b6ef680388c2348426cf2806c654dd7` |
| `UpperBound.lean` | `ee7492132b678566ee9e469ef82dbf05b093a312ab0a9fb2c7d924748418ff9b` |
| `Roots.lean` | `7fffa2a17da8f95efbed76576d811cbef697cf438fd89572c9e21b9cc2ee676b` |
| `Witness.lean` | `0be43789e90d1e7c08805505785b51f09dc93af2fc693da3180b92462f7a8db3` |
| `Sharpness.lean` | `b060361e4b821e51f23353a8a0d097e429e29cc17bca7a3a9b7f48257b020b97` |
| `Proof.lean` | `3c2c79e3fad910e1f1af1e919805006bf05d3b267e4aee47263c51c81e6c2691` |
| `Solution.lean` | `8f62fed09962a25854d795227de81f88f277780207b48064cdb36b2aefe336d3` |
| `NUMERICAL_TARGETS.md` | `f0d052c0d6041ce9b22b804d3d13c1fc1d4a74b48b02b2b85ad2715c343654f0` |
| `comparator.json` | `640a5c0c1285346f6f09bec7260d4f204308ea711396c0688e9230574be46aa7` |

My separate evidence is in [proof-referee-1-evidence](proof-referee-1-evidence/). Run, from this project:

```
python3 reviews/proof-referee-1-evidence/fresh_review.py
python3 reviews/proof-referee-1-evidence/inspect.py
python3 reviews/proof-referee-1-evidence/final_audit.py
```

The first script creates a fresh object prefix and explicitly removes the previous project object directory from `LEAN_PATH`. It freshly elaborated Definitions, Modulus, UpperBound, Roots, Witness, Sharpness, Proof, Solution, and the separately isolated Challenge: **nine successful commands**. There were no implementation warnings or errors. The Challenge produced exactly its eight intended placeholder warnings. This is local macOS source elaboration using clean, precisely pinned dependency sources and matching compiled dependency caches, not a fresh compilation of all dependencies. The environment, exact commands, source/object/log hashes, and all raw outputs are retained. Ten dependency repositories remained clean at their declared revisions.

Proof and Solution passed **16 explicit LeanCert kernel assertions** and corresponding transitive axiom reports, each exactly `propext`, `Classical.choice`, `Quot.sound`. My independent inspector passed another **12 kernel assertions** on the eight public theorems and four material internal results. It also inspected actual theorem kinds and traversed both types and bodies of **100 reached safe project declarations**, rejecting project axioms and unsafe declarations. It required **35 actual mathematical dependencies**, including the square-root uniqueness, Euclidean-norm, primitive-root, PSD, decomposition, witness, and least-element results discussed below. These were found in the actual elaborated terms. A separate lexical scan found no implementation admission, custom axiom, native evaluation, unsafe declaration, or Challenge import. The lexical scan supplements the kernel checks; it does not replace them.

The eight Solution signatures equal the eight frozen Challenge signatures after whitespace normalization, in the exact Comparator order. Actual elaborated types were also inspected. The config permits only the standard three axioms and has an empty definition-exception list. This local comparison does not claim the authoritative sandboxed Comparator has run.

## Fidelity and actual proof path

1. **Modulus, order and norm.** `matrixModulus A` really is `CFC.sqrt (A.conjTranspose * A)`, definitionally Mathlib's `CFC.abs A`. I inspected the pinned definitions and the actual `abs_nonneg`, `abs_mul_abs`, `norm_abs`, and `sqrt_unique` APIs. Gram positivity supplies the domain condition, including for singular and zero matrices. `operatorNorm` is the norm of `Matrix.toEuclideanCLM A`; `operatorNorm_eq_l2` connects it to the correctly scoped L2 matrix norm. The latter is not the default entrywise matrix norm. Genuine `Matrix.PosSemidef` means Hermitian with all complex quadratic forms nonnegative, and the matrix-order instance has exactly this meaning.

2. **Contraction and universal upper bound.** The norm-one criterion for positive C-star elements gives `0 ≤ |A| ≤ I`. The positive product used for `|A| - |A|²` has an explicit proof that its factors commute. Thus the proof does not make the invalid inference that arbitrary products of PSD matrices are PSD. The ordered-pair variance expands to `k Σ A* A - S* S`, with the factor one half handling double counting. Each summand is a genuine Gram matrix. The shifted square is a square of a Hermitian matrix. The exact decomposition and these positivity results give `k · errorGap ≥ 0`; division uses the proved positive scalar `k`. There is no external inequality premise. The proof retains every positive dimension and all complex contraction tuples.

3. **Every-k witness.** The root is the actual complex exponential `exp(2πi/k)`. The pinned primitive-root theorem and its geometric-sum consequence prove unit norm and the full zero sum for every `k ≥ 2`. No finite selection of k values is substituted. The actual vectors are `(1/2, sqrt(3)/2 · ω^j)`, and the matrices are `e₁ vⱼ*`. Their complex inner products, Euclidean vector norms, Gram matrices, reverse Gram matrices and operator norms are proved. The proposed modulus `vⱼ vⱼ*` is PSD and idempotent, so `CFC.sqrt_unique` identifies the actual positive square root. The source's modulus formula is a conclusion, not an axiom or a weaker bespoke definition.

4. **Exact sums and sharpness.** The complex finite sums, including the conjugated phases, give `Σ Aⱼ = (k/2) P` and `Σ |Aⱼ| = diag(k/4, 3k/4)`. The first sum is PSD, so its actual CFC modulus equals itself. Hence the difference is `diag(k/4, -3k/4)`. The proof specializes an arbitrary member of the complete admissible set to this genuine dimension-two contraction family. Its PSD gap has nonnegative first diagonal entry, whose real part forces `c ≥ k/4`. This uses no restricted admissible family in the definition.

5. **Attainment before infimum.** `sharp_constant_proved` constructs `IsLeast (admissibleConstants k) (k/4)` from the universal upper bound and the preceding lower bound. The pinned `IsLeast.csInf_eq` is the order-dual least-element theorem, with membership supplying nonemptiness and the least bound supplying boundedness. Thus the arbitrary conventions for an empty or unbounded real infimum cannot prove this target spuriously. The original odd-k theorem follows by specializing the stronger all-k result; its unused odd premise is a deliberate strengthening, not an assumption omission. The original n≥1 and k≥3/odd ranges remain in the final target.

The source's supplementary three-dimensional Hermitian construction and formal rank classification are outside the eight exports. Those are explicitly excluded in the source map and are not needed to resolve the canonical odd-summand question. The formalization proves the upper bound itself, so it does not depend on accepting a cited upper-bound theorem.

## Tau Ceti angles, reuse and computation

I applied the repository's adaptation of the ten review angles at [Tau Ceti Review `afb424ed`](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b). The exact cached rubric bytes and 14 inspected primary Mathlib/LeanCert files are hash-bound in the evidence; the latter match their immutable dependency Git blobs. Tau Ceti's separate roadmap admission and compatibility policies are not requirements of this NLA submission.

The scope is one complete permanent problem. The implementation separates definitions, modulus facts, the universal upper bound, roots, the witness, sharpness and public exports. It reuses the actual CFC, C-star order, PSD, Euclidean norm, primitive-root and infimum APIs instead of creating substitute analytic notions. The local adapter lemmas have material consumers. A focused pinned-source search also finds `Matrix.vecMulVec_mul_vecMulVec` as an alternative route for the short `outerProduct_mul` adapter; the present elementary identity proof is valid and small, so this is a possible simplification rather than a correctness or publication blocker. There is no broad `import Mathlib`, speculative infrastructure, or dependence on another problem's unmerged proof.

The exact all-k finite-sum argument eliminates numerical phase evaluation, interval subdivisions, numerical matrix square roots and case enumeration over k. `fin_cases` is confined to the fixed two-dimensional witness. **LeanCert is used for explicit kernel trust auditing of a pure exact proof; no interval certificate is needed or claimed.** I inspected its actual axiom classification and `#assert_trust` implementation, which rejects admissions, custom axioms and native execution assumptions in kernel mode. The final proof materially consumes the exact mathematical lemmas; no unused numerical certificate is presented as evidence.

Names and exported conclusions reflect the actual results. The main declarations and source correspondence explain the mathematical role of the implementation. Source attribution identifies Matthew J. Colbrook for the mathematical proof, Bourin and Lee for the original conjecture and prior bounds, and George Stepaniants for formalization with AI assistance and the approved Caltech department affiliation. Apache licensing is retained. I found no added George email or unsupported human-review/priority claim.

## Publication boundary and limitations

The frozen README, source map and numerical plan still describe their historical statement-first stage. The proof-completion note accurately describes the implemented result. Before publishing the Linux candidate, archive the historical README and replace the current README with truthful completed-local-proof wording, while preserving the already frozen mathematical/source records. Add the actual v0.4 manifest, complete both final reviews, and run the real Linux sandbox/Comparator/default-kernel gate before any Lean-verified promotion. This is a packaging prerequisite already planned by the author, not a mathematical change request.

No mathematical input, config, pin, canonical page, source proof, ID or status was changed in this review. All 101 frozen project inputs, eight original sources and 27 statement inputs remain byte-identical. Local checks cannot substitute for the authoritative Linux execution and its independent operational audit. Subject to those remaining gates, this frozen proof is approved.
