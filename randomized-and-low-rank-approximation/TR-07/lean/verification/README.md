# TR-07 verification record

Verified revision: [`4aa20f0e6ad92037a616c81fa8b1d7f57abca2dc`](https://github.com/marcusdavidwebb/OpenProblemsInNLA/tree/4aa20f0e6ad92037a616c81fa8b1d7f57abca2dc/randomized-and-low-rank-approximation/TR-07/lean).
The statement was frozen before proof implementation at `1b27d9f8`.
The complete proof was committed at `81001424`; its 36 proof inputs are
unchanged in the verified revision and current packaging.

## Recorded checks

- [Local build](local-build.log), 28 September 2026: `lake build Solution Challenge`
  passed (3233 jobs). The only warning is the deliberate independent Challenge placeholder.
  A repeat build and axiom audit on 29 September also passed for identical source.
- [Transitive axiom audit](axioms.log): the complete theorem and ten bridge
  results use only `propext`, `Classical.choice`, and `Quot.sound`.
  [Check.lean](Check.lean) is the audit input.
- [Statement hashes](STATEMENT_SHA256.json) and [proof hashes](PROOF_SHA256.json)
  bind the frozen boundary, source, comparison configuration, toolchain and dependency pins.
- [Repository checks](repository-checks.log): published-base permanent-ID
  validation and 17 ID tests, 30 Lean selection tests and 12 harness tests pass.
- [Independent reviews](../reviews/): two nonauthor AI agents approved
  the frozen statement before proofs and the complete final mathematical
  source. Both performed independent full builds and transitive axiom audits;
  their dated addenda inspect the actual Linux evidence and final documentation.

The authoritative fresh unprivileged Ubuntu check **passed** on 29 September
2026 in [run 36544197412](https://github.com/marcusdavidwebb/OpenProblemsInNLA/actions/runs/36544197412).
The catalog initiated this CI run and inspected its retained public evidence;
it did not execute a Linux sandbox on the macOS development host.

- [Comparator log](linux-36544197412/verify-20260929T084153Z-3983/comparator.log):
  fresh builds, matching statements, default-kernel acceptance, and
  `Your solution is okay!` with exit status zero.
- [Machine-readable result](linux-36544197412/verify-20260929T084153Z-3983/result.json):
  `comparator-accepted`, the exact repository commit, all input hashes,
  pinned tool receipt, and permitted axioms. All 36 frozen proof inputs
  match the current source and `PROOF_SHA256.json`.
- [Sandbox probes](linux-36544197412/verify-20260929T084153Z-3983/sandbox.log),
  [kernel controls](linux-36544197412/verify-20260929T084153Z-3983/kernel-controls.log),
  and [Comparator controls](linux-36544197412/verify-20260929T084153Z-3983/comparator-controls.log)
  pass. The `sorryAx` and native-axiom negative controls are rejected as required.
- [Artifact provenance](linux-36544197412/PROVENANCE.json),
  [original artifact ZIP](linux-36544197412/artifact.zip), and
  [artifact hashes](linux-36544197412/SHA256.json) bind the downloaded evidence.
  Its ZIP SHA256 matches GitHub's published artifact digest.

The later packaging changes add evidence, reviewer addenda, canonical
documentation and completion metadata. They leave all 36 proof inputs
unchanged. The complete checked result supports the catalog status `Lean verified`.

## Reproduction

From the project directory, with the pinned toolchain:

```sh
lake exe cache get
lake build Solution Challenge
lake env lean verification/Check.lean
```

From the repository root on supported unprivileged Linux:

```sh
python3 -m pip install -r tools/lean/requirements.txt
python3 tools/lean/validate_manifest.py randomized-and-low-rank-approximation/TR-07/lean
tools/lean/bootstrap.sh /tmp/nla-tr07-checker
tools/lean/verify.sh randomized-and-low-rank-approximation/TR-07/lean /tmp/nla-tr07-checker
```

The unchanged repository harness performs fresh isolated compilation,
statement comparison, transitive axiom checks and kernel replay with
rejection controls. No custom axiom, trusted native evaluation or numerical
certificate is used.
