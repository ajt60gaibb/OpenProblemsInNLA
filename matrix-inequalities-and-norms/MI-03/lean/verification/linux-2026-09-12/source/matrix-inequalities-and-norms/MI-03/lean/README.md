# MI-03 — complete Lean proof, Linux verification pending

**The complete odd-summand sharp-constant conjecture is proved in Lean, with all eight reviewed exports.** Two independent statement approvals preceded implementation; two independent final proof approvals and their exact evidence are listed in the candidate manifest. Actual Linux sandboxed Comparator/default-kernel verification and its independent operational audit are still pending. The canonical entry remains **Solved**.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. **Matthew J. Colbrook** retains authorship of the mathematical proof and result. **Bourin and Lee** retain the original conjecture and prior-bound credit. The implementing agent `/root` is not counted as either independent final referee.

The full [canonical target](../README.md) concerns every tuple of complex contractions in every positive matrix dimension. `matrixModulus A` is the genuine principal positive square root of A* A; `operatorNorm` is the genuine Euclidean operator norm. The sharp constant is the actual real infimum of the complete set of nonnegative admissible constants. The proof establishes **IsLeast of that full set at k/4 for every k≥2**, then identifies its infimum. This proves the entire original every-odd-k≥3 conjecture.

## Exact proof and scope

[Modulus](NLA/MI03/Modulus.lean) proves actual CFC positivity, the square identity, norm preservation and contraction bounds, including singular and zero matrices. [UpperBound](NLA/MI03/UpperBound.lean) proves the source's positive decomposition for arbitrary complex matrices. Half the ordered-pair Gram sum represents the source's unordered-pair variance; the remaining terms are the positive contraction defects and shifted square. This gives the universal bound without an external literature inequality as a premise.

[Roots](NLA/MI03/Roots.lean) proves the actual complex exponential root's unit norm and vanishing power sum for every k≥2. [Witness](NLA/MI03/Witness.lean) and [Sharpness](NLA/MI03/Sharpness.lean) construct the genuine two-dimensional rank-one matrices e₁vⱼ*, prove their Euclidean operator norms are one, identify their true CFC moduli vⱼvⱼ*, and compute the exact full sums. Their modulus difference is diag(k/4,−3k/4). Testing the first diagonal entry of the original admissibility inequality forces every admissible c≥k/4. [Proof](NLA/MI03/Proof.lean) obtains actual attainment and IsLeast before the sInf equality; no empty-set or unbounded-below convention is used.

The original canonical statement and Colbrook manuscript at revision `c0601d8825e9f9e744212c62e6a43fefc1c60a22` remain unchanged. [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) and [SOURCE_MAP.md](SOURCE_MAP.md) retain their frozen statement-stage wording as historical records. The source's additional three-dimensional Hermitian extremizers and rank classification are outside these exports; the complete original problem is covered.

[Solution](Solution.lean) exports these eight exact [Challenge](Challenge.lean) signatures, with prefix `NLA.MI03.`:

- `modulus_semantics`
- `contraction_modulus`
- `positive_decomposition`
- `universal_upper_bound`
- `root_of_unity_data`
- `sharpness_witness`
- `sharp_constant`
- `odd_contraction_conjecture`

## LeanCert, computation and reproduction

**LeanCert performs explicit kernel trust auditing of a pure exact proof. There is no numerical interval certificate.** Symbolic all-k sums and the positive-square identity avoid numerical phase approximation, interval subdivision and growing matrix enumeration. Proof and Solution explicitly select `leancert.trust "kernel"` and assert kernel trust for all sixteen internal/public results. All transitive axiom reports contain exactly `propext`, `Classical.choice` and `Quot.sound`; no admissions, custom axioms or native execution trust occur in the solution closure. The eight deliberate Challenge placeholders remain isolated and are never imported by Solution.

The project pins Lean **4.33.1**, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. The [manifest](lake-manifest.json) pins all ten dependencies. [Comparator](comparator.json) selects every public export, permits only the standard three axioms and has no definition exceptions. The [v0.4 formalization manifest](formalization.yaml) records scope, attribution, automation and exact reviews.

From this project directory, build the complete proof explicitly:

```
lake build Solution
```

The unchanged default target is Challenge; plain `lake build` therefore checks statements. The author's [fresh source checks](verification/author-completion/) elaborate all eight implementation/public modules in a new prefix and then inspect their actual proof dependencies. They pass all sixteen kernel/axiom checks, inspect 95 reached project declarations and require 25 material mathematical dependencies. The earlier complete Lake proof build passed with 3041 graph jobs. Local checks reuse clean pinned dependency caches on macOS; they do not claim to run Linux Comparator or rebuild all Mathlib sources.

## Independent reviews and remaining gates

- Statement referee 1: [report](reviews/statement-referee-1.md).
- Statement referee 2: [report](reviews/statement-referee-2.md).
- Final proof referee 1: [report](reviews/proof-referee-1.md).
- Final proof referee 2: [report](reviews/proof-referee-2.md).
- [Proof-start record](verification/proof-start.json), [author completion](reviews/proof-completion.md) and [complete proof freeze](reviews/proof-freeze.json).

The independent AI-agent referees apply the [pinned Tau Ceti adaptation](../../../docs/lean/REVIEW.md), including original-target fidelity, actual semantics, proof quality, reuse, documentation and attribution. These are not external human peer reviews or official Tau Ceti endorsements. Schiffer and Forsythe are credited as organizational/tooling references in the source map and manifest; no mathematical result from those projects is assumed.

Actual sandboxed Linux Comparator/default-kernel replay, its controls, an independent operational audit and publication review remain required by the [shared workflow](../../../docs/lean/README.md) and [harness](../../../tools/lean/HARNESS.md). No project-specific Linux result or immutable submitted revision is claimed yet.

Candidate packaging archives the original frozen README at [README.statement.md](verification/candidate-2026-09-12/README.statement.md). Only the current README changes among the 101 proof-freeze inputs. All other 100 inputs and all eight original source files remain identical; every frozen mathematical statement, proof, pin, configuration and earlier review record is preserved. The current guide describes completion; frozen statement-stage labels remain historical.
