# TR-14: Exact rank of complex Hankel tensors

The main document is **TR14_solution.pdf**. It contains a self-contained proof of an affirmative answer to TR-14 and a stronger exact-rank formula. Its editable mathematical source is `source/TR14_solution.tex`.

For a nonzero order-m, dimension-n complex Hankel tensor, set D=m(n−1). Let r be the rank of the middle Hankel catalecticant, and let s count the distinct projective zeros of a smallest-degree binary apolar polynomial. The formula proved in the manuscript is

    ordinary rank = symmetric rank
                  = min(D − r + 2, (m − 1)r − (m − 2)s).

The smallest apolar degree is r. In the balanced case D=2r−2 the minimal polynomial may not be unique, but the formula always returns r. The zero tensor has rank zero.

The manuscript also proves equality of ordinary, symmetric, and Vandermonde border ranks with r, and the sharp maximum Hankel rank (m−1)(n−1)+1.

## Proof and verification status

This is a new mathematical argument supplied for TR-14, not a claim that the repository or a journal has accepted the result. It has not been independently peer reviewed or formalized in a proof assistant. The universal proof is in Sections 2–5; the border-rank proof is in Section 6. The computational checks are supplementary and do not independently establish a universal tensor-rank lower bound.

The key contextual product-space lemma is proved in full. It does **not** assume that a nonreduced algebra has finitely many subalgebras: the Frobenius constraint rules out nilpotents in the particular auxiliary algebras used in the argument. `PROOF_AUDIT.md` explains this point and the remaining proof dependencies.

## Contents

| Path | Contents |
|---|---|
| `TR14_solution.pdf` | 13-page manuscript: theorem, proof, examples, algorithms, source notes |
| `source/TR14_solution.tex` | Editable LaTeX source |
| `PROOF_AUDIT.md` | Hypothesis-by-hypothesis proof audit and limitations of the checks |
| `SOURCES.md` | Primary-source inventory and attribution |
| `code/hankel_rank.py` | Exact rational-input rank algorithm |
| `code/binary_certificate.py` | Exact implicit algebraic-root Vandermonde decomposition certificates |
| `code/verify_solution.py` | Apolar, Fourier, Koszul, and mixed-graph regression checks |
| `code/verify_certificates.py` | Characteristic-zero verification of full tensor decompositions |
| `checks/` | Recorded successful test outputs |
| `examples/` | Moment vectors, computed ranks, and decomposition certificates |
| `requirements.txt` | Pinned Python packages used for the recorded runs |
| `reproduce.sh` | One-command rerun of all checks |
| `build_pdf.sh` | Optional LaTeX rebuild |
| `MANIFEST.sha256` | Integrity checksums for the delivered files |

No external papers or font files are bundled.

## Reproduce the checks

The recorded runs used Python 3.13.5, SymPy 1.14.0, and NumPy 2.3.5. Use Python 3.11 or later with the pinned packages. A virtual environment is recommended.

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
bash reproduce.sh
```

The new outputs go into `reproduced_checks/`; the delivered logs in `checks/` are not overwritten. Do not run the verification scripts with Python's `-O` optimization flag, which disables assertions. No network connection is needed after installing the dependencies.

The recorded checks comprise 162 exact apolar/rank-algorithm regression cases, 96 root-of-unity congruence cases, 128 exact integer Koszul identities with finite-field rank checks, 3,081 finite-field tensor-entry reconstruction checks, a mixed-root graph/stabilizer check, and 1,053 original tensor entries verified over exact rational polynomial quotient rings in 10 decomposition certificates. Zero tensors and rejection of floating-point moments are also tested.

These categories have different meanings. In particular, the 162 rank-algorithm cases are regressions of the formula and its invariants, not 162 independent computations of unrestricted tensor rank.

## Compute a rank

The moments use zero-based tensor indices:

    H[i1,...,im] = h[i1+...+im],    0 <= ik < n.

For the maximum-rank ternary cubic with h₂=1:

```sh
python code/hankel_rank.py -m 3 -n 3 \
  --moments '[0,0,1,0,0,0,0]'
```

The answer is ordinary rank 5, symmetric rank 5, and border rank 3. Rational entries may be written as JSON strings, such as `"7/3"`. Floating-point JSON numbers are rejected; the software does not infer exact rank from a numerical tolerance.

For the mixed double-point example with exact rank 7 and Vandermonde rank 8:

```sh
python code/hankel_rank.py -m 5 -n 3 \
  --moments-file examples/mixed_double_and_two_simple_moments.json
```

## Produce and verify an algebraic decomposition certificate

```sh
python code/binary_certificate.py -m 5 -n 3 \
  --moments-file examples/two_double_points_moments.json \
  --verify-full-tensor --output two_double_points_certificate.json
```

A certificate gives rational polynomials P, U, and a polynomial vector f. Its meaning is

    H = sum over all roots beta of P
        [U(beta)/P'(beta)] * f(beta)^(tensor m).

P is monic and squarefree. Root values are not approximated. Lagrange interpolation turns verification into exact polynomial remainders. An invertible rational shear handles roots initially at infinity. All polynomial coefficient arrays are in ascending powers.

The certificate generator gives an optimal **Vandermonde** decomposition. This need not be an optimal ordinary or symmetric decomposition: the JSON field `optimal_ordinary_and_symmetric` explicitly reports the distinction. When the local upper bound is smaller, use the Chinese-remainder/root-of-unity construction in Proposition 3.1; the manuscript proves its optimality by the same universal lower bound. The supplied rank algorithm applies only to rational input, while the mathematical theorem is over all of C.

## Rebuild the PDF

A standard LaTeX installation with `pdflatex` and the packages listed in the source is sufficient:

```sh
bash build_pdf.sh
```

The rebuilt PDF is placed in `build/`. The delivered PDF remains unchanged. File checksums can be verified from this directory with `sha256sum -c MANIFEST.sha256` (or `shasum -a 256 -c MANIFEST.sha256` on macOS).
