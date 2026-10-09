# KE-03 verification record

Proof revision: [`0b61bc859f622a69204f8705445c144095e4446d`](https://github.com/marcusdavidwebb/OpenProblemsInNLA/tree/0b61bc859f622a69204f8705445c144095e4446d/eigenvalues-and-inverse-problems/KE-03/lean).
The statement was frozen before proof implementation at `9862d2bd`; its bytes remain unchanged.

## Recorded checks — 28 September 2026

- [Local build](local-build.log): `lake build Solution Challenge` succeeded. Only the trusted comparison Challenge contains a deliberate placeholder.
- [Transitive axioms](axioms.log): the complete theorem and ten bridge results use only `propext`, `Classical.choice`, `Quot.sound`. [Check.lean](Check.lean) is the audit input.
- [Statement hashes](STATEMENT_SHA256.json) and [proof hashes](PROOF_SHA256.json) bind the source, comparison configuration, toolchain and dependency pins.
- [Repository checks](repository-checks.log): permanent-ID validation, 17 ID tests, 30 project-selection tests and 12 harness tests pass. The actual harness configuration preflight also passes.
- [Two independent AI-agent reviews](../reviews/README.md) approve the complete mathematical formalization and record separate compiler/axiom reruns.

The local logs are macOS development evidence. The authoritative Ubuntu check **passed** on 28 September 2026 in [run 36428948274](https://github.com/marcusdavidwebb/OpenProblemsInNLA/actions/runs/36428948274) for the exact proof revision. The catalog initiated this CI run and reviewed its retained public record; it did not run the Linux sandbox on the macOS host.

- [Comparator log](linux-36428948274/verify-20260928T133106Z-3899/comparator.log): fresh builds, matching statements, default-kernel acceptance, and `Your solution is okay!` with exit status zero.
- [Machine-readable result](linux-36428948274/verify-20260928T133106Z-3899/result.json): `comparator-accepted`, exact commit and all input hashes, pinned tool receipt, and permitted axioms. All 19 frozen proof inputs match the current source.
- [Sandbox probes](linux-36428948274/verify-20260928T133106Z-3899/sandbox.log), [kernel controls](linux-36428948274/verify-20260928T133106Z-3899/kernel-controls.log), and [Comparator controls](linux-36428948274/verify-20260928T133106Z-3899/comparator-controls.log) pass. The `sorryAx` and native-axiom negative controls are rejected as required.
- [Artifact provenance](linux-36428948274/PROVENANCE.json), [original artifact ZIP](linux-36428948274/artifact.zip), and [artifact file hashes](linux-36428948274/SHA256.json) bind the downloaded evidence. Its ZIP SHA256 matches GitHub's published artifact digest.

Later packaging changes add review reports, evidence, canonical documentation and truthful completion metadata. They leave all 19 proof inputs unchanged. The complete reviewed result supports the catalog status `Lean verified`.

## Reproduction

From a fresh checkout, using the pinned toolchain:

```sh
cd eigenvalues-and-inverse-problems/KE-03/lean
lake exe cache get
lake build Solution Challenge
lake env lean verification/Check.lean
```

From the repository root on supported unprivileged Linux with the real sandbox:

```sh
python3 -m pip install -r tools/lean/requirements.txt
python3 tools/lean/validate_manifest.py eigenvalues-and-inverse-problems/KE-03/lean
tools/lean/bootstrap.sh /tmp/nla-ke03-checker
tools/lean/verify.sh eigenvalues-and-inverse-problems/KE-03/lean /tmp/nla-ke03-checker
```

The unchanged harness performs fresh isolated compilation, statement matching, permitted-axiom checking, raw kernel replay and rejection controls. A build or mathematical review alone does not replace that check. No custom axiom, native evaluation trust, numerical certificate or modified verification infrastructure is used.
