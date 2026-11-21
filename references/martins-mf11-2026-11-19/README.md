# MF-11: Pedro Martins's negative-resolution claim

**Author:** Pedro Martins. **Preprint publication:** 15 November 2026.
**Catalog assessment and reproduction:** 19 November 2026.

[Primary preprint](https://doi.org/10.5281/zenodo.24237543) ·
[Retained manuscript](manuscript.pdf) ·
[Issue #385](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/385) ·
[Original target](../../matrix-functions-and-stability/MF-11/README.md) ·
[Assessment and fresh logs](verification/README.md)

## Result and exact target

Theorem 1.3 (p. 2) of *Marginal Growth Rates of Matrix Products Need Not Be
Weakly Increasing or Regularly Varying* reports a negative answer to both
MF-11 questions. Sections 2-5 (pp. 4-13) construct and analyze a pair of real
20-by-20 matrices depending on an explicitly defined Liouville number.
The maximum Euclidean operator norm over all words of length n satisfies
n <= g(n) <= 6n^3, hence the pair has joint spectral radius one.

For p_1 = 4, p_(j+1) = 4^(p_j), and N_j = 16^(p_j), the theorem gives

```text
g(N_j/2) / g(N_j) >= 2^(p_j) / (400000 p_j^4),
g(l N_j) / g(N_j) >= (l-1) 2^(p_j) / (400000 p_j^4),
```

for every j >= 2 and every integer l >= 2. The first bound refutes a
fixed weak-increase constant by comparing times N_j/2 and N_j; the second
refutes weak upper regular variation for the fixed multiplier l = 2.
The finite real pair is compact and nonempty, and the norm and all-word
maximum match the original entry. No assumptions of invertibility or a
prescribed growth rate are needed in the catalog target.

Theorems 1.4-1.7 additionally report invertible and almost-linear examples
and positive results for restricted families. These are additional claims
in the manuscript; the proposed catalog status depends only on Theorem 1.3.
The finite scripts' checks of those extensions are not a proof audit of them.

## Retained sources and provenance

- `manuscript.pdf`: the 35-page PDF attached to issue #385, byte-identical to
  `__TITLE____2_.pdf` in Zenodo record 24237543. Its SHA-256 is
  `0ab5ee46184d88cf60a49497fd99dc6cdebcf3fc6b31e9e16ff0da19762b4c52`.
- `verify.py`, `invertible_blocks.py`, `almost_linear.py`: unchanged copies
  of the three supplementary scripts in that Zenodo record. Each downloaded
  file matched the record's MD5 checksum; SHA-256 identities are also retained.
- `MF11_lean.zip`: the unchanged issue attachment. `MF11.lean` is its sole
  source file, extracted without modification.
- `zenodo-record.json`: the downloaded public metadata, including the
  publication date, file URLs, original checksums and CC BY 4.0 license record.
- `SHA256SUMS`: identities of these retained source inputs.
- `requirements.txt`: the numerical-package versions used for the reruns.
- `verification/`: assessment, full script outputs and execution environment.

The exact public downloads were:

```text
https://github.com/user-attachments/files/34887065/__TITLE____2.pdf
https://github.com/user-attachments/files/34887057/MF11_lean.zip
https://zenodo.org/api/records/24237543
https://zenodo.org/api/records/24237543/files/__TITLE____2_.pdf/content
https://zenodo.org/api/records/24237543/files/verify.py/content
https://zenodo.org/api/records/24237543/files/invertible_blocks.py/content
https://zenodo.org/api/records/24237543/files/almost_linear.py/content
```

The Zenodo metadata describes the work as a preprint. No journal acceptance,
external human peer review, author affiliation or priority claim is inferred.
The manuscript discloses Claude assistance in drafting/editing and writing
verification scripts, with the author retaining responsibility for the work.

## Reproduction

From this directory, with Python 3 and a temporary virtual environment:

```sh
python3 -m venv /tmp/mf11-reproduction
/tmp/mf11-reproduction/bin/python -m pip install -r requirements.txt
/tmp/mf11-reproduction/bin/python -I -u verify.py
/tmp/mf11-reproduction/bin/python -I -u invertible_blocks.py
/tmp/mf11-reproduction/bin/python -I -u almost_linear.py
shasum -a 256 -c SHA256SUMS
```

Use the default script parameters and keep assertions enabled. The scripts
mix exact rational identities with floating-point and multiprecision tests.
They do not enumerate all words at the very large dip lengths or prove the
infinite sequence of counterexamples computationally. The analytical proof
is essential. See the [recorded scope](verification/README.md).

## Status and formalization

The proposed status is **Solution claimed**, matching the author's request.
The catalog review checks correspondence, follows the main construction and
estimates, and reproduces the finite diagnostics. It is not presented as an
independent full-result proof audit or external human peer review.

The Lean attachment includes explicit 20-by-20 matrix definitions, growth
definitions, `MF11.MF11_negative_answer_spectral`, `MF11.dips_spectral` and
`MF11.MF11_answer_is_no`, followed by axiom-printing commands. The attached
ZIP supplies only the source file, with no `lean-toolchain`, Lake manifest,
pinned dependencies or successful verification/axiom log. The file was
inspected but not compiled or kernel-checked here. The presence of those
declarations and commands is not a successful formal-verification record.
No **Lean verified** status is asserted.
