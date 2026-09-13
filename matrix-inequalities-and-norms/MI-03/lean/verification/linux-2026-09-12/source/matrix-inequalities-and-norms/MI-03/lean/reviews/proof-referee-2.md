# MI-03 independent final proof referee 2

**Verdict: APPROVE / PASS for the frozen mathematical formalization.** No mathematical correction is requested. This is an independent AI review by `/root/leancert_examples`, dated 12 September 2026. I authored neither the candidate statements nor their proofs; my earlier statement review preceded implementation. I independently read the complete original problem and Colbrook proof, all definitions and eight signatures, every implementation module, the actual imported APIs, and the proof terms described below.

This applies the repository's adaptation of Tau Ceti Review at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`; it is not an official Tau Ceti review or human peer review. Correctness, full scope, generality, proof quality, reuse, API, naming, placement, documentation and attribution were examined. The pinned rubric/API identities and independent raw evidence are in [proof-referee-2-evidence](proof-referee-2-evidence/).

## Bound candidate and gates

- Proof completion: `919751e1f0595efd095250f2a6b2690b3214c96d988665fb7404d30690f2a729`.
- Proof freeze: `fcff9e256a6425853b15def24260b419613a72d9122c0a5bedea4b4cd5f0fd1d`. All **101 project inputs and eight original sources** match; originals were also compared with the actual Git blobs at `c0601d8825e9f9e744212c62e6a43fefc1c60a22`.
- All **27 previously approved statement inputs** remain unchanged. Both earlier approval hashes and the record of proof absence before implementation were checked independently.
- Definitions: `12f5c9c25dc68e0032679b76cb9d328279ce803b4de437db8e1a564c499c7de6`.
- Challenge: `6d7905413c8234a816c79287e58eddcf0ff6267c043336392744c3e30b68fb34`.
- Final proof module: `3c2c79e3fad910e1f1af1e919805006bf05d3b267e4aee47263c51c81e6c2691`.
- Solution: `8f62fed09962a25854d795227de81f88f277780207b48064cdb36b2aefe336d3`.
- Evidence manifest: `7422f5c308563fd2e343a107f1aaf4c7dc060c09b4f03638f2e59fd4a9c99ea0`.

The original universal odd-summand problem is retained. The stronger result for **every natural k ≥ 2** implies it, with every positive dimension, every tuple of complex contractions, actual Euclidean operator norms, principal positive square-root moduli, and the full set of admissible real constants. The proof establishes a least element before evaluating `sInf`; it does not exploit an empty-set/default value. No numerical or spectral conclusion has been inserted as a hypothesis.

## Mathematical inspection

The modulus is genuinely `CFC.sqrt (Aᴴ * A)`. Its identification with `CFC.abs`, positivity, square and norm identities use the actual Mathlib statements. For a contraction, the proof obtains `|A| ≤ I` from its norm, and proves `|A|(I−|A|)` positive using **commutation**. This is not an invalid assertion that arbitrary positive matrices have positive products.

The upper bound is the source's exact decomposition. With `S = ∑ Aⱼ`, `T = ∑ |Aⱼ|`, `R = |S|`, the implemented identity is

```
k ((k/4) I + T − R)
  = k ∑ (|Aⱼ| − |Aⱼ|²)
    + (1/2) ∑ᵢ ∑ⱼ (Aᵢ − Aⱼ)ᴴ (Aᵢ − Aⱼ)
    + (R − (k/2) I)².
```

Every term's positivity is proved. The final square is that of a Hermitian matrix; the ordered double sum has the correct factor one half. The positive factor `1/k` is justified by `k ≥ 2`. Singular, zero and nonnormal contractions are covered. No finite example stands in for this all-dimension proof.

For sharpness, the proof uses the actual complex exponential primitive root of order k, with its norm and geometric sum proved for arbitrary k. The vectors `(1/2, (√3/2)ωʲ)` have norm one. Their outer products yield actual Gram projections, and `CFC.sqrt_unique` identifies the genuine moduli. The C-star norm identity and the Euclidean operator-norm bridge establish that each witness matrix has norm one. Exact root sums give `S = (k/2)e₁e₁*`, `T = diag(k/4,3k/4)`, and `|S|−T = diag(k/4,−3k/4)`.

An arbitrary admissible c is then applied to this dimension-two tuple. Positivity of the first diagonal entry forces `c ≥ k/4`. This arbitrary-c conclusion, together with upper-bound membership, establishes `IsLeast`; the actual library `IsLeast.csInf_eq` is consumed only afterward. The final odd-k theorem is a consequence of this complete stronger result. The source's additional dimension-three Hermitian extremizers and classifications are correctly outside the eight exports.

## Independent mechanical and dependency checks

My separate driver compiled **ten commands**: Definitions, Modulus, UpperBound, Roots, Witness, Sharpness, Proof, Solution, the frozen Challenge, and a new actual-term inspector. Each exited zero. A new object prefix was used, and the previous project object directory was explicitly removed from `LEAN_PATH`. All target modules were re-elaborated; the only warnings were the eight deliberate holes in the separately checked Challenge, which Solution does not import.

All **eight exported source signatures** match the frozen Challenge, and Comparator selects exactly these names with `definition_names = []`. The 16 internal/public `#assert_trust kernel` and axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. My independent transitive traversal reached **95 project declarations** and required **31 material consumed dependencies**, including the real CFC, norm, primitive-root, positive-decomposition, witness, lower-bound and infimum bridges. These checks examine actual dependencies, not merely the presence of theorem names in source.

LeanCert is used for the explicitly approved **kernel trust audit only**. I inspected the pinned command implementation: it checks collected axioms and rejects admissions, custom axioms and native-execution trust. This exact proof has no interval certificate, and none is claimed. No proof module contains an admission, custom axiom, unsafe declaration or native-decide shortcut. All ten dependency source trees are clean at their exact recorded revisions, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

I also reran my independent exact `Q(√3,i)` transcription diagnostic for k = 2,3,4,6,12 and a noncommuting, nonunit k = 5 tuple. The Gram, sum, variance and decomposition checks pass without floating arithmetic. These finite diagnostics supplement the checked universal proof and are not its justification.

## Quality, attribution and remaining publication gate

The modules separate actual modulus facts, universal positivity, arbitrary roots of unity, the concrete witness and sharpness. Library CFC/order/norm/root facts are reused. Existing `vecMulVec` multiplication and conjugate-transpose APIs were inspected; the short argument-specific outer-product adapters have real consumers and do not introduce a competing matrix theory. The fixed Challenge/Solution export layer is the repository's verification interface, not a compatibility shim. The exact decomposition avoids interval subdivision and numerical spectral computation entirely.

Matthew J. Colbrook's mathematical proof attribution and Bourin–Lee conjecture/prior-bound credit are preserved. George Stepaniants receives the approved formalization credit with the Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. No George email is added.

**D1, publication-only:** the frozen statement-stage README still says “Statements only; proof not implemented.” Root acknowledged this and will archive/refresh that README during candidate packaging, while identifying NUMERICAL_TARGETS and SOURCE_MAP as the historical approved statement plan. Do not publish the stale status prose. It does not alter this approval of the frozen mathematical files; I made no edits to them.

This was a macOS Lean 4.33.1 review reusing matching compiled dependency objects, **not** a full dependency-source rebuild, a Linux run, or the sandboxed Comparator gate. Actual Linux kernel/Comparator and controls, final truthful metadata, and independent publication review remain required. No canonical status, commit, push or PR action was performed by this referee.
