# Complete canonical source check, 18 October 2026

All 42 actual canonical Lean sources compiled into a new isolated output directory,
using only the ten git-revision-checked pinned dependency caches. No shared NLA
project object path was supplied. All 38 copied modules match their shared source
and both lock digests, including all 36 proof modules. The unchanged Challenge
warns about its one deliberate placeholder; the actual Solution exports the full
Target with kernel trust and only propext, Classical.choice, Quot.sound.

Reproduce from repository root with installed pinned dependency/toolchain caches:

```bash
python3 eigenvalues-and-inverse-problems/SP-11/lean/verification/check_package.py --dependency-root /absolute/lean-statements --lean-bin /absolute/lean-4.33.1/bin --output /absolute/fresh-evidence-directory
```

The actual original cache/toolchain locations, all dependency hashes, every source
hash, every executed Lean command, exit status and log hashes are in result.json.
This is a fresh direct Lean source check, not a lake build, independent approval of
author-owned modules, or isolated Linux Comparator receipt. Each raw module log is
retained beside the result. The final Linux gate must run the existing unmodified
repository verifier on the committed canonical package.
