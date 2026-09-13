# MI-16 research proof dossier

## Mathematical content and scope

The main document is `paper/mi16_dossier.pdf`; its complete LaTeX source is beside it.

**General spectra:** Theorem 2.1 gives a finite exact algebraic prescription for the maximum permanent on every positive-semidefinite complex unitary orbit. An explicitly specified critical-value elimination polynomial supplies a finite candidate list. An exact Schur-character formula supplies a spectral moment, and an explicit finite moment-order bound selects the correct candidate. The proof does not assume that all real critical values of the complexified problem are Hermitian-feasible.

This is an algebraic/algorithmic answer, **not a compact general closed form, an efficient arbitrary-order solver, or a classification of general optimizers**. Generic algebraic optimization is an established methodology. No claim of historical novelty, independent peer review, or acceptance by the MI-16 maintainers as the intended resolution is made. A structural all-spectrum formula remains unachieved in this dossier. These qualifications appear on the first page of the report, not only here.

**One exceptional eigenvalue:** For every `n >= 2` and `alpha,beta >= 0`, Theorem 8.1 proves

\[
M_n(\alpha,\beta,\ldots,\beta)
=\max_{k\in\{2,n\}}\sum_{j=0}^{k}\binom{k}{j}j!\beta^{n-j}
 \left(\frac{\alpha-\beta}{k}\right)^j.
\]

The report gives every equality case. For `0 <= alpha < beta`, write `x=(beta-alpha)/beta`. There is one transition `x_n` between the full-support and two-coordinate-support optimizers. It satisfies

\[
x_3=3/4,\quad x_4=2-2\sqrt3/3,\quad x_n\uparrow1,
\qquad 1-x_n=\frac1{2n}+\frac3{8n^2}+O(n^{-3}).
\]

In particular, `M_n(0,beta,...,beta)=beta^n/2` for every `n >= 2`.

## Attribution to the uploaded findings

`input_findings_MI16/` preserves the five MI-16 files from the uploaded pack, unchanged. The permanent expansion for a rank-one perturbation of a scalar matrix and the reduction to a maximum over **all** support sizes `1,...,n` are from those findings. The reduction to supports **2 or n**, the threshold/equality analysis, and the all-spectrum critical-value/moment construction are developed in this report. The general commutator stationarity condition and the algebraic/representation-theoretic tools are credited to prior sources.

## Reproduce the checks

Python 3.10 or later is required. The exact core needs only SymPy and the Python standard library.

```bash
python -m pip install -r requirements.txt
python code/verify.py
python code/verify_selector.py
python input_findings_MI16/verify_exact.py
```

The supplied main run passed **12,832 exact checks**. The separate selector run tests seven small end-to-end cases and the full conservative moment order `p=1296` for spectrum `(1,3)`, using an independent exact integral expansion. The original pack verification was rerun successfully as well. JSON records are in `verification/`.

These are exact arithmetic regression checks, not proof-assistant certification or enumeration of all orders. The general mathematical arguments are in the PDF.

## Runnable examples

```bash
# Exact structural formula; returns 1/2, support 2.
python code/one_exceptional.py 7 0 1

# The tie case in dimension 3; returns 17/32, supports 2 and 3.
python code/one_exceptional.py 3 1/4 1 --transition

# Exact spectral moment; returns 307/126.
python code/spectral_moments.py 0 1 2 --moment 2

# Critical-value elimination; returns (z-3)(z-5).
python code/critical_values.py 1 3

# End-to-end algebraic prescription with a rigorous early exit; returns 5.
python code/exact_algebraic.py 1 3
```

The exact reference programs accept **rational** inputs. The mathematical theorem is stated for all nonnegative real eigenvalues; effective evaluation for arbitrary real inputs presupposes exact field arithmetic and comparisons.

## Resource limits and failed computation

The algebraic prototype deliberately limits generic elimination to order two by default and limits moment enumeration. A budget exception returns **no mathematical answer**. Raising the guards can cause very expensive computation.

An unrestricted elimination trial for `(0,1,2)` was terminated at a 180-second process limit before producing a polynomial. The timeout is recorded in `provenance/computational_limitations.json`. No general order-three elimination success or high-order end-to-end success is claimed. This does not affect the separate analytic proof or the exact order-three moment calculations.

The optional `exploration/` directory contains floating-point local searches used only for hypothesis testing. Their objective values are not certified global maxima and are not used as proof.

## Build the PDF

A TeX distribution with `amsmath`, `amsthm`, `lmodern`, `microtype`, `geometry`, `xurl`, and `hyperref` is sufficient.

```bash
cd paper
pdflatex -interaction=nonstopmode -halt-on-error mi16_dossier.tex
pdflatex -interaction=nonstopmode -halt-on-error mi16_dossier.tex
```

## Package integrity

`MANIFEST.sha256` lists hashes of the delivered files. `provenance/sources.json` records the mathematical sources and the uploaded archive's hash. The PDF was compiled and visually inspected after rendering. Its exact preflight record is in `verification/pdf_quality.json`.

The manifest covers the delivered files; rerunning scripts updates the verification JSON records and therefore changes their hashes.
