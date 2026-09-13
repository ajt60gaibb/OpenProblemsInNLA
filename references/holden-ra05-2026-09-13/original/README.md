# RA-05: all-exponent lower bounds and a negative answer to the proposed formula

Prepared September 12, 2026 for Sidney Holden with ChatGPT.

**Start with `manuscript/RA05_all_p_lower_bounds.pdf` (19 pages).**

## Result and scope

Let `S_p(k, epsilon)` be the worst-case minimum number of nonzero, nonnegative original-row weights needed to preserve every subspace cost of dimension at most `k` within relative error `epsilon`.

The manuscript proves, for each fixed real `p > 2` and all sufficiently large `k`,

```text
S_p(k, epsilon) >= c_p k^(p/2) / (epsilon^beta_p + log(k)/k),

beta_p = 2                  for p = 4, 6, 8, ...,
beta_p = 2 - 2/p            for all other p > 2,
0 < epsilon < 1/2.
```

For every fixed `p > 2`, this rules out every universal bound of the form

```text
C_p (k^(p/2)/epsilon + k/epsilon^2) log(2k/epsilon)^c_p.
```

The counterexample family has `d = k+1` and polynomially many rows. Each input works for all accuracies in the stated range. Weights may depend arbitrarily on the complete input; the theorem is not limited to an algorithm or random sampling rule.

For even `p >= 4`, the new lower bound and the upper bound cited in RA-05 match up to logarithms when

```text
sqrt(log(k)/k) <= epsilon < 1/2.
```

**This is not a full classification of the optimal joint size for all `p` and all accuracies.** The proposed formula receives a complete negative answer, but the broader first sentence of RA-05 still has quantitative gaps. The manuscript, `STATUS.md`, and `PROOF_AUDIT.md` identify those gaps without labeling the whole classification solved.

These are research proofs with internal checks, not independently peer-reviewed or proof-assistant-verified results. The sole non-elementary structural input to the principal lower bound is the precisely stated restricted-invertibility theorem in Theorem 2.2 of the manuscript.

## Contents

| Location | Contents |
| --- | --- |
| `manuscript/RA05_all_p_lower_bounds.pdf` | Full proofs, consequences, explicit quartic counterexample, probability appendices, and references. |
| `manuscript/RA05_all_p_lower_bounds.tex` | Editable LaTeX source. |
| `PROOF_AUDIT.md` | Dependency-by-dependency audit and common invalid shortcuts avoided. |
| `STATUS.md` | Exact completed and uncompleted portions of the canonical problem. |
| `REPRODUCIBILITY.md` | Commands, tested environment, and numerical limitations. |
| `SOURCES.md` | Primary source locations, versions, and provenance. |
| `code/ra05.py` | Finite-difference identities, product costs, derivative matrices, finite-field bases, and hyperplane witnesses. |
| `code/verify.py` | Reproducible exact checks and numerical diagnostics. |
| `results/verification.json` | Complete recorded results. |
| `results/verification.txt` | Test-run transcript. |
| `results/quartic_r4.npz`, `results/quartic_r16.npz` | Explicit matrices, half-supported candidate weights, and normalized violating hyperplane normals. |
| `results/p3_diagnostic_instance.npz` | A small illustrative non-even-power instance; not the large-r existence construction. |
| `prior_work/RA05_counterexample.pdf` | Earlier quartic-only manuscript, included unchanged for comparison. |
| `SHA256SUMS.txt` | Checksums of the distributed files, excluding the checksum file itself. |

## Reproduce

From this directory, with Python 3.10 or newer:

```bash
python -m pip install -r requirements.txt
./run_checks.sh
```

The supplied run passed **2,851 assertions**. Exact rational and integer tests check finite algebraic identities. Floating-point tests check particular matrices and scalar inputs. None of these tests stands in for the universal proofs.

Build the PDF using a LaTeX installation with the packages named in its preamble:

```bash
make pdf
```

Read a concrete quartic witness:

```python
import numpy as np

z = np.load("results/quartic_r16.npz", allow_pickle=False)
A, w, normal = z["A"], z["weights"], z["normal"]
full = np.sum((A @ normal) ** 4)
weighted = np.sum(w * (A @ normal) ** 4)
print("support:", np.count_nonzero(w))
print("normal norm:", np.linalg.norm(normal))
print("relative error:", abs(weighted - full) / full)
# The query subspace is the hyperplane orthogonal to `normal`.
```

No GitHub plugin was used. No repository issue, pull request, or status edit was submitted.
