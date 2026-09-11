# Tensor-computations candidate submission package

This package contains five full-target candidate proofs or counterexamples and one separately qualified TT-SVD result. These are proposed submissions for mathematical review, not a claim of independent peer-review acceptance. No submission has been sent.

## Claims and scope

| Target | Status | Claim |
|---|---|---|
| TR06 | Full-target candidate proof | Finiteness of average angular CP-decomposition conditioning under the hypotheses stated in the manuscript. |
| TR15 | Full-target candidate counterexample | A counterexample to the stated Hankel-tensor eigenvalue-inclusion conjecture. |
| TR17 | Full-target candidate proof; generic scope | The generic-rank target for odd-order Hankel tensors, as formulated in the manuscript. |
| TR19 | Full-target candidate proof | The discriminant-degree target stated in the manuscript. |
| TR20 | Full-target candidate proof | Both discriminant-degree formulas stated in the manuscript. |
| TR04 | Qualified result; not a uniform-factor improvement | A tie-aware TT-SVD construction meeting the displayed pointwise strict inequality, with the qualifications in the manuscript. |

**Read `QUALIFICATIONS.md` before using or submitting the results.** In particular, TR-04 does not improve the uniform worst-case factor, and TR-17 does not assert the generic rank for every Hankel tensor.

## Contents

`proofs/` contains the mathematical manuscripts in Markdown. `tex/` contains the LaTeX sources and common preamble. `pdf/` contains any successfully compiled manuscripts. `code/verify_results.py` contains the reproducible checks. `results/` retains the computed outputs and console logs. `submission/` contains an unsent cover note and reviewer guide. `audit/` records the claim boundaries, all 26 targets, repository provenance, build status and software environment. `SOURCES.md` indexes source references.

## Reproduce the checks

Use Python 3 in an isolated environment, install the recorded dependencies, and run:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python code/verify_results.py
```

The dependency versions in `requirements.txt` are those present when the package was assembled. The retained verification output is supplied for comparison. Passing the script is not a formal proof of the general theorems.

The packaging-time verification invocation recorded exit code `None`. Its complete standard output and errors are in `results/packaging_verification_console.txt` and `results/packaging_verification_run.json`.

## Build the manuscripts

With a LaTeX installation providing `pdflatex` and the packages used in `tex/preamble.tex`, run:

```sh
./build_pdfs.sh
```

0 manuscripts compiled successfully during packaging. See `audit/pdf_build_status.json` for the per-file result. Sources remain available independently of the PDF build.

## Provenance and submission

Repository: https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/tensor-computations. Snapshot: `not recorded`. Exact per-problem links are in `SOURCES.md`. Consult the repository's current contribution instructions before submitting.

The five full-target manuscripts and the qualified note should be reviewed independently. No result is claimed for the other 20 targets. No complete novelty certification, external referee approval, or uninterrupted three-hour active-work duration is asserted.

`SHA256SUMS.txt` provides content hashes of the deliverable files. `submission/COVER_NOTE_DRAFT.md` is ready for review and addition of the submitting researcher's identity, not for automatic dispatch.
