# Current verification guide — SP-08

From this problem directory:

```bash
python verification/spread_exact.py verify certificates/SP-08_n8_a-half.json
python verification/spread_exact.py verify certificates/SP-08_n10_a0.json
python verification/spread_exact.py verify certificates/SP-08_n11_a0.json
python verification/check_taylor_certificates.py certificates/SP-08_n8_a-half.json certificates/SP-08_n10_a0.json certificates/SP-08_n11_a0.json
python verification/reference_integer_check.py certificates/SP-08_n8_a-half.json
```

All of these commands were run successfully during this audit. The first three
check all certificates **and regenerate every pattern and characteristic
polynomial**, comparing full coefficient sets. The direct-binomial checker is a
separate implementation of the root-bound checks, using only Python integers;
it does **not** replace coverage. The last command reconstructs all 5,648 n=8
representative matrices and checks their polynomials with scalar arbitrary-
precision Faddeev-LeVerrier arithmetic. That full secondary representative check
was not run for n=10 or n=11, although the main verifier cross-checks one matrix
per batch in all dimensions and includes a proved int64 overflow bound.

The main `verify` command calls no floating-point eigensolver. The `generate`
command uses numerical eigenvalues only to propose endpoints, then accepts them
only after integer certificate validation. Generation commands and historical
resource notes are preserved in `PRIOR_VERIFICATION_GUIDE.md`; its old root paths
are historical, not the current directory layout.

Current logs: `recheck_n8.log`, `recheck_n10.log`, `recheck_n11.log`,
`taylor_certificate_tests.log`, `recheck_n8_reference.log`. Earlier logs are
under `prior_logs/`. PASS means exactly the named local test, never independent
agent/human review or formal verification. All mathematical correspondence
still depends on the proof in `../proof.md`.
