Independent canonical isotropic-package review — approved

The immutable package at `6c607ab14af2b8b2b8075f0b3f1798e037c10899`, under `tensor-computations/TR-26/lean`, faithfully exports the single literal theorem `NLA.Proofs.TR26.isotropic_degree (d) (hd : 2 ≤ d)`. Its type is `HasReducedDegree d (2*d) (IsotropicImage d)`, using the unchanged full incidence ideal, original unweighted Veronese cone and complex bilinear denominator. No substantive package finding remains. This approval does not cover the later full-source checkpoint.

The independent replay passed **1143 checks and 49 retained command records**: 40 fresh runtime source compilations, one fresh audit of all 288 declarations (219 actual theorems and 69 actual definitions), three genuine negative controls, four fresh pinned Comparator-library module compilations and one actual library execution. The endpoint is an actual theorem and its transitive axiom set is exactly `propext`, `Classical.choice`, `Quot.sound`. The exact endpoint consumer, literal live-versus-reviewed Target `rfl`, and absence of nonisotropic/full-Target proof exports pass. The reference `sorryAx`, counterfeit proof-valued definition and custom oracle all reject at their intended gates.

The actual Comparator library imports `Challenge` and `Solution` into **separate environments**, compares the exact exported signature and referenced definitions, accepts the solution's standard-three closure, and rejects the actual reference hole. These are executions of the pinned Forsythe library at `8d1b0c0545a77b40245e84705aa7d273e6c81e62`; `definition_names` is empty and the only selected theorem is the isotropic endpoint. This is not the Comparator CLI, exporter, Linux sandbox, or an exported raw-kernel replay.

All **353 locked inputs**, plus the lock itself, match immutable Git bytes and lengths. All **117 provenance copies**, including **36 shared runtime Lean sources** from independently approved checkpoint `4692336f0e1a50d5e261bba68277875da30fba51`, match their recorded source objects. All **221 bound review files** match; the copied non-author REVIEW/result/APPROVAL are verbatim. There are 76 `.lean` files in the package: 40 runtime sources and 36 historical source snapshots under `reviews/`; the latter are not runtime imports. All 24 preapproved originals, registry entries, canonical README and mathematical targets remain unchanged. The `04045bad` descendant changes only the generated inventory outside the package. Metadata and README retain canonical status `Solved` and explicitly deny whole-problem/nonisotropic verification at this frozen package.

This packaging review reuses the already approved exact mathematical source reading of checkpoint 4692336f while freshly compiling all its shared sources. That proof establishes the **raw** isotropic image equation, including nonzero cone scalings, infinity exclusion by actual denominator value, `d=2`, zero numerator and nonzero numerator-kernel matrices. Packaging adds no endpoint assumptions. The four runtime wrappers and partial reference were read in full; Solution imports the proved endpoint and does not import Challenge.

The build used pinned Lean 4.33.1 (compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) on macOS arm64, private fresh project objects, and a read-only dependency cache. All ten manifest package revisions and tracked cleanliness passed before and after. No author project objects were used. Linux PR369 and any later full-target package require their own source-bound evidence.

Two reviewer-only setup failures are preserved under `attempts/`: an escaped-identifier repair to the generated declaration-kind consumer, and adding the pinned Lean binary directory to PATH for runtime `findSysroot`. No authored bytes changed. All 40 source commands had already actually returned exit zero; their observed commands/logs and source/object hashes are retained in FIRST_SOURCE_REPLAY.json. Only the repaired consumer/remaining controls and then the runtime runner were executed again; AUXILIARY_REPLAY.json retains those actual intermediate commands. A clean reproduction uses the default driver without resume arguments.

Evidence: `result.json`, `reproduce_package.py`, `FIRST_SOURCE_REPLAY.json`, `AUXILIARY_REPLAY.json`, `logs/`, `consumers/`, `tool-sources/`, and `source-lock.json`. Private source/object prefix is `/private/tmp/nla-tr26-isotropic-package-6c607ab1-verification`.

Reproduce from a new owned build directory:

```sh
python3 reproduce_package.py \
  --repo /Users/ajt253/Documents/OpenProblemsInNLA \
  --lean /private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean \
  --packages /Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages \
  --build /private/tmp/nla-tr26-isotropic-package-reproduction-NEW \
  --output /private/tmp/nla-tr26-isotropic-package-evidence-NEW
```
