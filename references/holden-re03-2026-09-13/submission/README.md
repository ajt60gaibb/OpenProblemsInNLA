> **Repository submission update — 2026-09-13:** Author: Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. A separate informal AI-agent audit passed the partial mathematical results; the full problem remains unresolved. See the [submission record](../README.md) and [independent review](../independent-review.md). The author field and continuation PDF have been updated; the original ZIP is retained one directory above. The text below records the original assembly state, and its “unreviewed”/“unchanged” descriptions refer to that original state. The checksum manifest now covers this edited copy.

# RE-03 continuation archive

**Status: unreviewed partial research results, not a full solution.**

This archive assembles the available continuation manuscript, editable sources,
reference code, recorded two-stage verification report, and unchanged earlier
package. It does not claim any new mathematical result or independent proof
verification. The unresolved factor of depth described in the manuscript remains.

## Contents

- `manuscript/re03_extended_results.pdf`: the 25-page continuation manuscript.
- `manuscript/re03_extended_results.tex`, `manuscript/two_stage.tex`, and
  `manuscript/accuracy_appendix.tex`: its complete LaTeX input files.
- `code/two_stage.py`, `code/peeling.py`, and `code/hodlr.py`: the available
  query-counted reference implementation and dependencies.
- `results/two_stage.json`: the original, unchanged recorded verification report.
- `PROOF_REVIEW.md`: the original review guide and outstanding proof obligations.
- `prior/RE03_partial_results.zip` and `prior/RE03_partial_results.pdf`: the
  earlier package and manuscript, preserved byte for byte.
- `provenance/README.previous.md`: the continuation's earlier README, unchanged.
- `ASSEMBLY_NOTES.md` and `STATUS.json`: the exact scope and missing-file notes.
- `SHA256SUMS.txt` and `verify_integrity.py`: a complete payload checksum manifest
  and an offline verifier.

## Important availability limitation

The earlier README and manuscript describe additional verification scripts,
auxiliary implementations, and result files that were not available among the
conversation attachments at assembly time. They have not been fabricated or
silently replaced. In particular, the continuation's `code/verify.py`,
`code/verify_two_stage.py`, `code/depth_family.py`, and
`code/joint_regression.py` are **not included**. Its full reported verification
suite therefore cannot be rerun from this archive. The available
`results/two_stage.json` is a historical record, not newly reproduced evidence.

See `ASSEMBLY_NOTES.md` for details. The README at this archive's root is the
current packaging guide; the previous README is retained only for provenance.
The manuscript is unchanged, including its original reproduction instructions.

## Read and verify

The supplied PDF can be read without installing any software dependencies.
After extracting, run from this directory:

```bash
python verify_integrity.py
```

This checks file hashes, not the mathematical correctness of the manuscript.
Verify before modifying or rebuilding packaged files.

## Run the available implementation checks

The recorded and assembly-check environment uses Python 3.13.5 and NumPy 2.3.5.
NumPy is the only Python package dependency for these checks.

```bash
python -m pip install -r requirements.txt
bash run_checks.sh
```

`run_checks.sh` runs the **new, limited assembly smoke checks**, not the missing
continuation verification suite. It writes to `rerun_results/` by default, leaving
recorded results untouched; another output directory may be supplied as its
first argument. These checks exercise imports, oracle query accounting, the
exact-projection fallback, and one experimental-width sketching example. They
do not prove the claimed randomized bounds. Their assembly-time results are in
`results/assembly_smoke.json`.

The earlier archive contains its own original `code/verify.py` and results.
It can be extracted separately to run that earlier suite. Do not confuse its
script with the missing continuation script of the same name.

## Rebuild the manuscript

With a suitable LaTeX installation and the packages named in the source:

```bash
bash build_pdf.sh
```

The helper builds in a temporary directory, performs three LaTeX passes, and
replaces only the continuation PDF after a successful build. It was added for
assembly; the supplied PDF has not been rebuilt or altered. Rebuilding changes
its checksum and makes the original integrity manifest obsolete for that file.

## Mathematical scope

The manuscript proposes lower and upper expressions

```
lower: min(n, k*L/epsilon + k/epsilon**2)
upper: min(n, k*L**2/epsilon + k*L/epsilon**2)
```

up to universal constants in the stated RE-03 model. The upper expression before
the n-query cap is L times the lower expression. The arguments are unreviewed;
this package is not a complete solution, formal proof certificate, or claim of
practical speedup. Floating-point checks do not certify exact-real theorems.
