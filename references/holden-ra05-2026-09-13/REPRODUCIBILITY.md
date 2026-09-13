# Reproducibility and file formats

## Running the checks

```bash
python -m pip install -r requirements.txt
./run_checks.sh
```

The wrapper pins numerical-library thread counts to one for small predictable test runs. The recorded run used the Python and library versions listed at the beginning of `results/verification.json`. The exact tested versions are also in `requirements-tested.txt`.

There are nine test suites, covering exact rational stencils, exact even-power extraction, high-precision scalar Taylor checks, the Gaussian comparison increment identity, a non-PSD derivative-kernel example, exhaustive small-subset singular-value checks for one small noise family, general product diagnostics, exact finite-field/MUB identities and quartic witnesses, and rational exponent comparisons.

A successful run prints one PASS line per suite and writes `results/verification.json`. The distributed run passed 2,851 assertions. The small-noise diagnostic separately enumerates all 2,324 subsets of sizes one to three of 24 vectors; its singular values are floating-point results.

Rerunning the program overwrites generated result files, so the distributed checksums may no longer match those result files because timing, library versions, and last-bit numerical details can differ.

## Interpretation

The principal large-dimensional random construction is proved to exist analytically. The script does not instantiate its large conservative dimension thresholds, verify all net points, or run an exhaustive search over all row weights.

The general core helper uses pivoted QR to find a small illustrative column set. It does not implement the imported restricted-invertibility proof, and does not assert that QR is a universal algorithm with the theorem's guarantee. Its measured singular value is recorded explicitly.

The finite-field identities are checked in integer arithmetic for r=4,16,64. The finite-difference identities and even-power extraction checks use exact rational arithmetic. The global Taylor checks use 100-digit arithmetic but still test only finitely many points. The text proof supplies the universal remainder bound.

## NumPy archives

All `.npz` files can be read with `numpy.load(path, allow_pickle=False)`.

`quartic_r4.npz` and `quartic_r16.npz` contain:

- `A`: the explicit real input matrix, with rows in group-major order;
- `weights`: one candidate nonnegative reweighting, supported on exactly half the rows;
- `normal`: a unit vector whose perpendicular hyperplane violates the target accuracy for that candidate;
- `integer_core`: the exact integer matrix T = sqrt(r) U used to construct the bases.

For these files, the normal has dimension `2*r`, and the query rank is `2*r-1`. The theorem in Section 8 is universal over all too-small supports; the saved weights merely exercise the witness extractor.

`p3_diagnostic_instance.npz` contains `A`, core `U`, noise `V`, candidate query vectors `Z`, rectangular derivative matrix `E`, two-dimensional group weights `weights`, and a unit query `normal`. This is a small diagnostic input, not the asymptotic existence theorem instantiated at its proven threshold.

## Building the manuscript

```bash
make pdf
```

The source uses standard LaTeX packages: geometry, fontenc, lmodern, amsmath, amssymb, amsthm, mathtools, microtype, booktabs, array, enumitem, xcolor, fancyhdr, hyperref, and bookmark. Two pdflatex passes build the references and table of contents.

The supplied final PDF was rendered with Poppler and visually inspected. The final LaTeX compilation had no overfull boxes, underfull boxes, undefined references, or LaTeX warnings. No font files are included in the archive.
