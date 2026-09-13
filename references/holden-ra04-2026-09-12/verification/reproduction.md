# Coordinating-agent reproduction — 2026-09-12

Python 3.12, NumPy 2.3.5, SymPy 1.14.0, mpmath 1.3.0 and threadpoolctl 3.6.0, macOS.

Commands from the package directory:

```sh
python tests/exact_checks.py --output verification/exact_checks.json
python tests/numerical_checks.py --output-dir verification/rerun
bash build.sh
```

Both scripts exited successfully. All seven exact groups passed, including 23 recursive identities. The full numerical run included high-precision probes; results are retained in `rerun/`. Experiments are selected finite instances, not a proof or universal-constant certificate. The independent analytic reviewer did not rely on these reruns.

Repository checks: permanent ID validation against origin/main passed; catalog generation passed; all 17 permanent-ID tests passed; global math formatting check passed. Canonical PDF and manuscript were rebuilt and visually inspected. No Lean checks performed.

The original supplied environment.json and results/ describe the author's run; this file and verification/ describe the separate local reproduction.
