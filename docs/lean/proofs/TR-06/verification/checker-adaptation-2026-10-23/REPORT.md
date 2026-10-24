# TR-06 strict actual Linux artifact checker adaptation

23 October 2026. This adapts the existing PF-05 checker into `../check-linux-artifact.py`. It is tooling preparation. **No actual TR-06 Linux artifact has been audited by this adaptation, and no CI acceptance report was generated.** Root source review precedes use on the real downloaded artifact.

All 41 inherited controls remain: actual GitHub workflow/job completion, exact workflow and harness commit, exact committed/current package inputs and file sets, original raw ZIP/GitHub digest/job-upload correspondence, artifact/run/head/extraction identity, pinned tool/source receipt and binaries, genuine Linux Lean/compiler identity, default verifier profile, actual Comparator default-kernel acceptance, proof-kind and LeanCert kernel consumer, standard axioms, native/sorry rejection, kernel/Comparator regression fixtures, and isolation/capability/network/filesystem controls. The eleven inherited log-marker lists are byte-for-byte unchanged.

The TR-06 selection is exactly the original ten published declaration names plus `NLA.TR06.target`, with no definition holes and exactly the standard three permitted axioms. Both actual generated proof-kind/kernel assertions and actual axiom records are required for every selected export. Long Lean log lines may wrap: the parser tolerates whitespace wrapping while requiring one record per selected theorem, exactly the standard three axioms, and no missing, duplicate or unexpected theorem record.

Four additional strict controls bring the total to **45**:

1. The source lock must contain exactly 140 distinct shared/canonical source copies: 80 completion proof modules, 58 retained modules and two statement modules. Each recorded hash must equal its actual committed and current shared and canonical bytes. All ten explicit build/boundary package exports must match their recorded hashes.
2. All 58 retained modules must equal actual bytes at immutable published commit `3da7a876b97815c99ebde0f4f9c17932096345a2`, the retained-source registry, committed/current shared copies and committed/current canonical copies. The complete published retained source path set must match exactly.
3. The original ten-name published Comparator configuration and entire published Challenge prefix must remain unchanged after removing only the added intrinsic import. The final Challenge must match the independently approved pre-Solution input lock, whose exact SHA-256 is fixed in the checker.
4. The reviewed mirror and Infrastructure must equal immutable original commit `36767fa430309f13d04dc6ebe080d470f5c2444a`; Identity must match the separately approved frozen input hash. The inherited original intrinsic Target-byte check remains in place.

The expected counts are explicit: **153 canonical inputs, 144 Lean inputs, 140 copied sources, 80 proof sources, 58 retained sources and 11 selected exports**. Both complete Git file-set checks remain. The checker requires its 45-control inventory exactly and exits unsuccessfully on any failed control. Original/current source correspondence is not inferred from a green workflow alone.

`validation.json` records successful syntax and CLI-help checks, all 41 inherited controls and unchanged log markers, the six focused parser cases, all eleven generated theorem-kind/kernel guards and 22 missing-guard rejection mutations. One parser case uses the actual local macOS canonical Solution log solely to validate its line format; it is explicitly not Linux evidence. No synthetic workflow/artifact success fixture was created.

The original baseline commits must be available locally for the historical byte checks. The checker reads retained data and Git objects; it does not download, reconstruct a Linux run or rerun Comparator. Once real completed-run metadata, original artifact ZIP and metadata, exact extraction and raw gzipped job log exist, use its required CLI arguments. Its output will then be an actual artifact audit bound to that exact commit and the current package. Descriptive package changes require their own fresh exact-input receipt.

No canonical package file, mathematical source, permanent ID or original artifact was edited by this task. The checker and this preparation evidence are outside the 153 canonical CI inputs.
