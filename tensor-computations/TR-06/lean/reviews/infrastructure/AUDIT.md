# TR-06 independent infrastructure and API audit

Reviewer: OpenAI Codex agent `/root/tr06_infrastructure_audit` (AI agent). Date: 2026-09-24. Scope: read-only infrastructure, dependency/API and example-project review. No TR-06 statement approval, mathematical proof approval, Linux Comparator result or complete-target verification is claimed. No repository files were changed.

## Existing infrastructure

The repository already has the shared reproducible infrastructure requested by the campaign: `docs/lean/README.md`, `docs/lean/REVIEW.md`, `tools/lean/{bootstrap.sh,selftest.sh,verify.sh,harness.py,projects.py,validate_manifest.py,source-lock.json}`, the pinned v0.4 manifest schema, and `.github/workflows/lean-verification.yml`. Existing verified TR-15 and TR-27 projects pin Lean 4.33.1, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Shared checker sources are hash-locked to Forsythe `8d1b0c0545a77b40245e84705aa7d273e6c81e62` (58 source files); old successful control logs are fixtures, not evidence about a new TR-06 proof.

The authoritative reproduction commands, on non-root Linux with the required real sandbox, are:

```sh
python3 -m pip install -r tools/lean/requirements.txt
python3 tools/lean/validate_manifest.py tensor-computations/TR-06/lean
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh tensor-computations/TR-06/lean /absolute/path/to/nla-lean-tools
```

`verify.sh` already runs the control suite before candidate verification. Running the separate `selftest.sh` is useful as the requested infrastructure-first gate but is not a mathematical result. Prerequisites: Linux, non-root account, Python 3, Git, elan, Go >=1.24, C compiler, `/usr/bin/bwrap`, user/mount namespaces and a working user systemd session. CI uses Ubuntu 24.04, Go 1.27.1, pinned setup/checkout/Lean actions, Bubblewrap, and `XDG_RUNTIME_DIR=/run/user/<uid>` / `DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/<uid>/bus`; see the existing workflow for exact setup. The verifier requires a committed unchanged project, materializes ordinary tracked HEAD files into a fresh copy, prepares pinned dependencies, runs real sandbox/rejection controls and checks candidate statement equality, transitive permitted axioms and default-kernel replay. It fails closed; macOS elaboration is only development evidence.

`comparator.json` must list every exported target, have empty `definition_names`, and permit only a subset of `propext`, `Classical.choice`, `Quot.sound`. `Challenge.lean` may contain deliberate trusted statement holes but the solution must not import it. Two independent statement approvals must precede implementation and bind actual definition/signature hashes. Final multiple-agent reports must distinguish fidelity, proof correctness, reuse/API/attribution; implementers do not count as their own independent referees.

`formalization.yaml` uses the pinned v0.4 schema (`99c678e569c7c4c0772db297c5ddd5e4c9b6322e`). The repository validator additionally requires zero development sorries, zero sorries in definitions, exact one-for-one result coverage of comparator theorem names, all result files present, and each result pointing to `comparator.json`. This validator is for completed project metadata; passing it does not establish truthful complete scope. George Stepaniants must receive Department of Computing and Mathematical Sciences, California Institute of Technology affiliation, without contact email. Preserve original Matthew J. Colbrook mathematical proof attribution separately. Actual costs, author endorsement, human review and Linux verification must not be invented.

## Actual installed Lean and pinned source evidence

Although Lean is not on PATH, a working development compiler exists:

`/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin/lean`

It reports Lean 4.33.1, arm64-apple-darwin24.6.0, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. A clean full Mathlib checkout is at `/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.lake/packages/mathlib`, HEAD `0df444a360eaa60ab8c11dca51a86af692955474`, matching TR-27's manifest. The GitHub recursive source tree was downloaded from `https://api.github.com/repos/leanprover-community/mathlib4/git/trees/0df444a360eaa60ab8c11dca51a86af692955474?recursive=1`, is untruncated, and every one of 8,321 tracked Mathlib source files matches the primary tree's Git blob hash. See `mathlib-tree.json` and `mathlib-api-audit.json`. This is actual complete pinned-source inspection, not absence of a local cache. No dependency rebuild was performed.

`APIProbe.lean` was elaborated by this compiler against existing pinned caches, exit 0. `APIProbe.log` prints exact signatures below and standard-three axiom closures for the linear volume and radial integrability results. `APIProbe-run.json` records compiler command, search path and exit code. An initial unqualified-namespace diagnostic is retained separately; it was corrected to `MeasureTheory.*`. This probe is not a proof of TR-06 and not fresh Linux verification.

## APIs actually available

- `Mathlib/Analysis/InnerProductSpace/NormDet.lean`: `LinearMap.normDet`, `LinearMap.normDet_sq` (line 295), `LinearMap.normDet_eq_prod_singularValues` (375), and `LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume` (434). The last theorem is the exact volume factor for a **linear map** between possibly different Euclidean dimensions; it does not prove the nonlinear graph area formula.
- `Mathlib/Geometry/Euclidean/Volume/Measure.lean`: `MeasureTheory.Measure.euclideanHausdorffMeasure` / `μHE[d]` (65), and equality to Euclidean Lebesgue volume in the matching dimension (190, 194). Use the Euclidean normalization or prove the relevant constant bridge; unqualified Mathlib `μH[d]` is not automatically the ordinary Euclidean-volume normalization.
- `Mathlib/MeasureTheory/Function/Jacobian.lean`: `MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image` and `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`. These concern differentiable injective maps `f : E → E`, same-dimensional Haar measure, and ordinary determinant. They are useful building blocks but not a theorem on the Hausdorff volume of a lower-dimensional graph `E → E × F`.
- `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:92`: `integrableOn_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s)`, conclusion `IntegrableOn (fun x => x ^ s * Real.exp (-b*x^2)) (Set.Ioi 0) volume`. This directly handles both required radial powers `k-2` and `k-1` once `k>1` is established. No LeanCert interval computation is needed for this analytic fact.
- `Mathlib/Geometry/Manifold/Riemannian/Basic.lean`: smooth tangent inner products, path lengths and the associated Riemannian metric/distance. It does not itself construct induced volume or prove manifold area/coarea.
- Hausdorff measure contains Lipschitz/anti-Lipschitz estimates and exact isometry/linear scaling; these may support future foundations but do not supply the full target via a direct invocation.

## Foundations not located in pinned Mathlib

Complete-source exact commands and their zero results are recorded in `mathlib-api-audit.json` and individual search text files. Case-insensitive searches include semialgebraic/SemiAlgebraic, Tarski–Seidenberg, Seidenberg, o-minimal, cell decomposition, area formula/coarea, and Riemannian volume. Together with inspection of the actual Hausdorff/Jacobian/NormDet/manifold APIs, this locates no existing semialgebraic-set formalization, projection closure, semialgebraic dimension/fiber theorem, bounded semialgebraic finite Hausdorff-volume theorem, or nonlinear manifold graph-area formula. Search absence is not a proof that no differently named derivation exists; it means those precise foundations cannot currently be claimed as existing imported theorems. An implementation must genuinely prove them or use another independently audited permitted-axiom library, rather than assuming them in a target structure.

The canonical TR-06 source uses exactly these absent theorem families: bounded semialgebraic graph finite volume; dimension equality under finite nonempty fibers; graph Jacobian dominates first derivative; nonlinear graph area with branch multiplicity; actual smooth identifiable tensor cone geometry and full-measure exceptional-set removal; induced-volume polar decomposition. The available scalar Gaussian integral is only the final radial factor. Proving that factor or an abstract theorem which assumes finite link derivative integral does not verify TR-06.

## Requested reference projects

Schiffer pinned revision `2938e277969c329caf154e48a3d8823f3635c7f1` was inspected through its complete untruncated GitHub tree (152 entries), actual `Schiffer/Challenge.lean`, and the reusable directory. That directory contains only `ImplicitProductReduction.lean` and its README, plus the umbrella import. Downloaded contents match primary pinned tree Git blob hashes (`schiffer-source-audit.json`). The reusable API packages local Lyapunov–Schmidt reduction for a product map using Mathlib's implicit-function theorem; it does not supply semialgebraic finite-volume, stratification, graph-area, or polar-volume foundations. Challenge demonstrates the trusted statement/import boundary and separation from implementation.

Forsythe pinned revision `8d1b0c0545a77b40245e84705aa7d273e6c81e62` was inspected through repository-retained exact Challenge and numerical-target reference snapshots and the shared source-lock/harness/NOTICE. Its directly reusable contribution here is the existing pinned numerical/checker workflow: independently reviewed Challenge signatures, exact numerical targets, `set_option leancert.trust "kernel"`, explicit `leancert (trust := kernel)`, `#assert_trust kernel`, isolated Comparator and permitted-axiom audit. No Forsythe mathematical result is assumed for TR-06, and no fresh full Forsythe source build is claimed.

Conclusion: Shared infrastructure can be reused as is. The local development toolchain is available. The principal TR-06 difficulty is genuinely missing theorem-level semialgebraic and geometric-measure foundations, not a numerical certificate or CI setup issue. A complete formalization must discharge them before status promotion.
