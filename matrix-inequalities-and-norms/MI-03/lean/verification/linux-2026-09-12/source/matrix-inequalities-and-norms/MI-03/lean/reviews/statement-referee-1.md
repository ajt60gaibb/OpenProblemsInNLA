# MI-03 independent statement referee 1

**Verdict: APPROVE the frozen statement boundary. No mathematical correction requested.**

Reviewed 12 September 2026 by independent agent `/root/formal_review_standards`. The statement author is `/root`; this referee did not author or edit the candidate definitions, declarations or mathematical plan. This is a statement review, not a proof approval, external human review, official Tau Ceti endorsement or Linux verification. Implementation must still wait for the second independent statement approval.

## Exact review identity

The reviewed [freeze](statement-freeze.json) has SHA256 `0243fca8b3e04b5dd3ee9d79f3fa9e25a4c706519089fbece2984178d11f7804` and binds **27 candidate files plus eight original sources** at repository revision `c0601d8825e9f9e744212c62e6a43fefc1c60a22`. All 35 files were independently checked before and after fresh elaboration; each original source also matches its exact Git blob at that revision.

| Input | SHA256 |
| --- | --- |
| `NLA/MI03/Definitions.lean` | `12f5c9c25dc68e0032679b76cb9d328279ce803b4de437db8e1a564c499c7de6` |
| `Challenge.lean` | `6d7905413c8234a816c79287e58eddcf0ff6267c043336392744c3e30b68fb34` |
| `NUMERICAL_TARGETS.md` | `f0d052c0d6041ce9b22b804d3d13c1fc1d4a74b48b02b2b85ad2715c343654f0` |
| Author handoff | `6c16f5c268ddcac6f7d738bd6494007c17dd660955870afefc1572bba09a9b86` |
| Complete original authored TeX | `2d2d0ac01e22de1c6d63471c0965b1c17362d5eda23d53cbf397ab4932be32b3` |

## Full target and actual definitions

I read the complete canonical README, original Colbrook proof, exported solution TeX, source correspondence and numerical plan. I also checked the primary [Bourin–Lee v3 text](https://arxiv.org/html/2307.02034v3#S4): its Corollary 4.4 treats general contractions and the conjecture after Remark 4.5 asks sharpness for every odd summand count greater than one. This source supports the target and attribution; the candidate does not assume its upper-bound theorem as an axiom.

`AdmissibleConstant k c` means an actual nonnegative **real** constant works in every positive natural dimension and for every tuple of complex square contractions. `errorGap` is exactly `cI + Σ|A_j| − |ΣA_j|`, and actual `Matrix.PosSemidef` is required. There is no fixed dimension, Hermitian-input, invertibility, normality, commutation or strict-contraction restriction. Zero and singular matrices are included.

The actual elaborated definitions and imported APIs were inspected, including fully explicit terms:

- `matrixModulus A` is `CFC.sqrt (A.conjTranspose * A)`, the principal nonnegative square root of the **right** Gram matrix. The imported `MatrixOrder` instance defines order by PSD differences. Actual `PosSemidef` includes Hermitian symmetry and all finite-support quadratic forms; on `Fin n` this covers every vector. Complex nonnegativity requires zero imaginary part as well as nonnegative real part.
- `operatorNorm A` uses the continuous linear map on `EuclideanSpace ℂ (Fin n)`. It cannot silently select the entrywise matrix norm. The witness-vector norm elaborates to `PiLp.instNorm` with exponent two. `Matrix.toEuclideanCLM_toLp` supplies the actual multiplication action, and the L2 operator-norm bridge is a definitional library equality.
- `sharpConstant` uses the actual real `sInf`. The `sharp_constant` obligation additionally requires `IsLeast` of the complete admissible set. Actual `IsLeast` includes membership and a lower bound against every member, so emptiness or an unbounded-infimum convention cannot provide the promised attainment. The set is also bounded below by zero directly from admissibility.
- `OddContractionConjecture` retains every natural odd `k≥3` and equality to real `k/4`. The supporting theorems quantify every `k≥2`. Excluding `k=1` is necessary: the single-summand constant is zero. Definitions at `k=0` do not create a loophole because every root or sharpness export carries `k≥2`.

## Audit of all eight required exports

| Export | Independent assessment |
| --- | --- |
| `modulus_semantics` | PSD, the genuine square identity and equality of actual operator norms are conclusions for arbitrary complex matrices. |
| `contraction_modulus` | The original norm bound is the only substantive hypothesis; both `I−|A|` and `|A|−|A|²` must be proved PSD, including singular cases. |
| `positive_decomposition` | The exact finite-sum identity is correct. Half the ordered pair sum is `kΣA_j* A_j−S* S`; each diagonal pair vanishes and each unordered pair occurs twice. The two claimed unconditional PSD terms are a sum of genuine Gram matrices and the square of a Hermitian matrix. Positivity of the remaining modulus term is not incorrectly claimed without contraction assumptions. |
| `universal_upper_bound` | Must prove the complete admissibility property without an external matrix-inequality premise. Multiplication by positive `k` can be removed after the decomposition and contraction bounds. |
| `root_of_unity_data` | Uses the actual `Complex.exp (2πi/k)` and all indices in `Fin k`. Pinned `Complex.isPrimitiveRoot_exp`, `IsPrimitiveRoot.norm'_eq_one` and `geom_sum_eq_zero` have precisely the required generic hypotheses. No finite table or approximate phase appears. |
| `sharpness_witness` | `outerProduct u v` really is `uv*`, with conjugation on the second vector. Every norm, modulus and sum identity is a conclusion about the actual matrices. The two-dimensional witness works for every `k≥2`, not a subsequence. |
| `sharp_constant` | The upper bound gives membership. Specializing any admissible constant to the actual two-dimensional witness and inspecting its first PSD diagonal entry forces `c≥k/4`. This establishes the advertised least element and genuine infimum. |
| `odd_contraction_conjecture` | The complete original proposition is the theorem conclusion; no omitted odd count or supplied sharpness hypothesis remains. |

The independent algebra audit reconstructed the witness with exact rational coefficients in `Q[s,z]/(s²−3,1+z+…+z^(k−1))`, where conjugation sends `z` to `z^(k−1)`. The deliberately different cases `k=2,3,5,9` check all unit-vector inner products, Gram/projection identities, exact sums, the diagonal difference and the ordered-pair decomposition. The script does not import the author's checker. These are transcription diagnostics, **not** a universal proof, numerical spectrum calculation, CFC proof or PSD/norm certificate. The generic Lean obligations remain essential.

The source's extra three-dimensional Hermitian extremizers and a theorem certifying witness rank are explicitly outside these eight exports. Neither is required by the canonical dimension-independent odd-summand target, which the proposed boundary covers completely.

## Independent execution and trust

[check.py](statement-referee-1-evidence/check.py) created a fresh random output prefix and excluded the existing project `.lake/build/lib/lean` from `LEAN_PATH`. It re-elaborated **Definitions, Challenge and the independent inspection**, all with exit code zero. Definitions and inspection emit no warnings. Challenge has exactly its **eight intentional `sorry` warnings**, and all eight placeholder axiom reports explicitly expose `sorryAx`; they have not been represented as proofs.

All **20 definition-level `#assert_trust kernel` checks** passed. Their transitive axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. Source inspection found no custom axiom, admitted definition, native-evaluation proof or implementation override. Comparator lists exactly the eight declarations, no definition exceptions, and exactly the standard-three whitelist. No Proof or Solution implementation exists. All **ten** dependency Git revisions equal the locked pins and their tracked sources are clean.

The initial independent inspection probe used one incorrect namespace for the primitive-root norm lemma. Definitions and Challenge already passed; only that diagnostic `#check` failed. The correction is confined to this referee's inspection script, and the complete successful fresh sequence and original failed probe are both retained. No candidate byte was changed.

These are local macOS checks reusing matching pinned dependency caches. They do not establish cache provenance, rerun every Mathlib source, or replace the later authoritative Linux isolation, Comparator and default-kernel replay gates.

## Referee standards, reuse and remaining gates

The pinned Tau Ceti rubrics were applied to correctness/faithfulness, generality, single-target scope, reuse, API, naming, documentation, placement and attribution as appropriate to this repository. The eight exports are useful explicit statement contracts; generic CFC/norm/root and infimum infrastructure already exists and should be reused, as recorded in the plan. No source-copying or uncredited mathematical dependency was found. Colbrook retains mathematical authorship; George Stepaniants receives formalization credit with the full Caltech department affiliation and no added email. Schiffer/Forsythe structural reuse and the absence of official endorsement are disclosed.

The symbolic square decomposition and exact roots of unity avoid artificial intervals or eigenvalue searches. LeanCert's intended role here is explicit kernel trust auditing, not an invented numerical certificate. No proof-quality or final consumed-dependency approval is possible before implementation. Two independent final proof reviews, actual Linux checking and truthful final metadata remain required after both statement approvals.

The [evidence manifest](statement-referee-1-evidence/EVIDENCE-MANIFEST.json), SHA256 `8183c2a305a42555ff171e1f62a3a45d0c3c0668d02c418babf6eb91f87ad924`, binds **18 evidence files**, including the initial probe. Only the exact outer manifest path is excluded from its own listing. Final inspection log: `eae72c8e6cc1b0326c1b6de728e1976860c9e8c42655fbbd42db387c73930d7f`; independent result: `b9177c5714c366f9966fe4801d2f39707e320fa9ebc15f42fbf6fa620a20cee8`; exact algebra result: `45782f1f79d80efd4016cab557fa59896c743abd55797338a79fbd6ea92a5553`. Source/API records and all raw commands are retained alongside them. No canonical, source, registry, commit, push or status change was made.
