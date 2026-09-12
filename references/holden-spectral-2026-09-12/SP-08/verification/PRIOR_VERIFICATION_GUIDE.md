# Verification guide

## Exact finite-case checks

Run from the archive root:

```bash
python verification/spread_exact.py verify certificates/SP-08_n8_a-half.json
python verification/spread_exact.py verify certificates/SP-08_n10_a0.json
python verification/spread_exact.py verify certificates/SP-08_n11_a0.json
```

Each command checks every rational or quadratic certificate, regenerates all
signed-threshold patterns and their exact characteristic polynomials, and
compares the complete sets. No eigensolver is called by the verifier. The
integer overflow bound is checked before 64-bit matrix arithmetic is used.
Some polynomials repeat; distinct polynomials suffice for a spectral bound.

For constrained execution environments, `--certificates-only` validates the
root certificates without regenerating coverage. That flag alone is not full
verification. The delivered order-eleven logs include one certificate-only
pass and a separate full regeneration of all 2,097,152 patterns, comparing all
222,013 coefficient arrays against the checked set. Both are necessary to
interpret the combined result as complete local coverage.

The JSON `generation_seconds` for the order-eleven file measures the final
certificate-generation phase from a previously computed exact enumeration
cache, not the earlier enumeration phase. The cache is not required to verify
anything and is intentionally not distributed. Earlier monolithic order-eleven
generation calls exceeded individual execution-call limits and were rerun in
these two stages; they are not being counted as successful complete runs.

## Regeneration from scratch

```bash
python verification/spread_exact.py generate --n 8 --low 1 --high 2 --out n8.json
python verification/spread_exact.py generate --n 10 --low 0 --high 1 --out n10.json
python verification/spread_exact.py generate --n 11 --low 0 --high 1 --out n11.json
```

Generation uses floating-point eigensolvers to propose rational endpoints, then
accepts only bounds proved with arbitrary-precision integer polynomial shifts.
The verifier is independent of those numerical suggestions. Failure to find an
enclosure produces a nonempty `failures` array and an `INCOMPLETE` claim label;
such a file is rejected by `verify`. The supplied final files have empty
failure arrays.

The generation routine accepts integer endpoints `low < high` with `high > 0`
and dimensions `n >= 2`, subject to its overflow check. Only the three supplied
cases have been established in this session. Successful execution elsewhere
still depends on the reduction proof and an audit of the implementation.

Memory use and output size grow quickly. The order-eleven exact JSON file is
large because it contains every distinct characteristic polynomial and its
certificate. There is no claim of polynomial-time general verification.

## Supplementary tests

```bash
python verification/algebra_checks.py
```

This runs exact rational identity tests for the symplectic reduction, exact
integer sign-pattern tests, exact rational displacement tests for KE-02, and
explicitly labeled floating-point smoke tests for the two-point spectral
matching formula. These examples are not substitutes for the analytical proofs.

The second implementation `direct_charpoly` in `spread_exact.py` uses
arbitrary-precision scalar Faddeev–LeVerrier arithmetic, rather than the batched
Newton power-trace implementation. One matrix in every enumeration batch is
cross-checked. This diagnostic does not replace the mathematical integer-safety
bound or an independent audit of coverage.

## Environment and meaning of PASS

Tested: Python 3.13.5, NumPy 2.3.5, SymPy 1.14.0.
Only NumPy is needed for the exact finite-case verifier. SymPy is needed for the
supplementary algebra tests. No scripts access GitHub or any network service.

PASS means the named local test completed. It does not mean independent agent
review, external human review, proof-assistant certification, novelty, or full
resolution of a repository target. Review hashes are not claimed; the archive
contains ordinary integrity hashes in `SHA256SUMS.txt`.

## Optional second polynomial implementation

```bash
python verification/reference_integer_check.py certificates/SP-08_n8_a-half.json
```

This script uses only the Python standard library, reconstructs each listed
representative matrix without NumPy, and computes its characteristic polynomial
by scalar arbitrary-precision Faddeev–LeVerrier arithmetic. It passed for every
one of the 5,648 order-eight representative polynomials. It can be run on the
larger files as well, but that additional full representative check was not run
for orders ten and eleven during this session. Full family coverage and the
integer certificate checks were run for those orders using the main verifier.
