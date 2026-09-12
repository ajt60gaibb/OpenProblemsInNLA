# IE-16: a negative solution

**The proposed inequality is false.** This package contains a complete analytic counterexample, an exact-arithmetic certificate for it, and a stronger theorem showing that no finite dimension-independent replacement constant exists.

Start with **[solution.pdf](solution.pdf)**. The manuscript is nine pages, including the proofs and references. Sections 1–3 resolve IE-16 directly; Sections 4–5 prove the stronger unboundedness result; Section 6 gives an explicit normal-matrix/initial-residual witness and explains the computation.

## The explicit counterexample

Use the definition in the linked problem:

\[
M_k(E)=\min_{\deg p\le k,\ p(0)=1}\max_{z\in E}|p(z)|,
\qquad
B_k(E)=\max_{S\subseteq E,\ |S|=k+1}M_k(S).
\]

Let

\[
\omega=-\tfrac12+\tfrac{\sqrt3}{2}i,\qquad
\varepsilon=\tfrac1{1000},\qquad
L=\{\omega^a+\varepsilon\omega^b:0\le a,b\le2\},\qquad k=4.
\]

There are nine distinct nonzero points, and the required degree range is satisfied. The manuscript proves

\[
M_4(L)=\frac{3003003000}{1001003001001}>0.00299,
\qquad
B_4(L)<0.0023.
\]

Consequently,

\[
\frac{M_4(L)}{B_4(L)}>\frac{13}{10}>\frac4\pi.
\]

The exact full-set minimizing polynomial is

\[
p_*(z)=1-\frac{1+\varepsilon}{1+\varepsilon+3\varepsilon^2+
\varepsilon^3+\varepsilon^4}z^3.
\]

Its optimality is proved twice: by symmetry and a one-variable convex minimization, and by positive weighted orthogonality. A Lagrange-interpolation argument bounds every five-point subset by considering the three possible cluster-occupancy profiles. Neither the counterexample nor its proof depends on a floating-point optimizer.

For orientation, the certified numerical values are approximately

```text
M_4(L)             = 0.002999994003011984982048
B_4(L)             = 0.002250559965550380002031
M_4(L) / B_4(L)    = 1.332998919794758294237943
4 / pi             = 1.273239544735162686151070
```

The decimal displays are rounded; exact rational interval endpoints are in the JSON certificate. For the same nine-point family, the ratio tends to `4/3` as the small-cluster scale tends to zero.

## The stronger conclusion

For every integer `r >= 1` and every positive `eta`, the manuscript constructs a finite admissible spectrum with

\[
n=3^r,\qquad k=(3^r-1)/2,\qquad
\frac{M_k(E)}{B_k(E)}>\left(\frac2{\sqrt3}\right)^r-\eta.
\]

The proof uses a three-cluster amplification lemma, separately establishing the full-set and subset limits for both residual and monic polynomial approximation. Since `2/sqrt(3) > 1`, the ratios are unbounded. Each example uses finitely many positive scales, which may be chosen rational. No infinite-depth limit is treated as a finite spectrum.

## Reproduce the finite certificate

Python 3.10 or later is sufficient. There are **no third-party Python dependencies**, no network requests, and no numerical optimization packages.

From the extracted package directory, run:

```sh
python3 code/verify.py
```

A successful run begins with:

```text
IE-16 EXACT-ARITHMETIC VERIFICATION: PASS
```

The command regenerates both files in `certificates/`. To use another output directory and a finer square-root enclosure, run:

```sh
python3 code/verify.py --digits 80 --output ./check_80_digits
```

The verifier represents all nodes in the field `Q(omega)` using rational coefficients. It checks distinctness, nonzero nodes, positivity and normalization of the weights, exact residual moduli, and all four weighted orthogonality identities. It then checks all `126 = binomial(9,5)` subsets. Square-root bounds use integer arithmetic; bounds on pi use rational alternating series and Machin's identity. All strict inequalities are tested as exact rational inequalities. The program raises an exception and exits unsuccessfully if a check fails.

## Package contents

| File | Purpose |
|---|---|
| `solution.pdf` | Complete typeset manuscript and references. |
| `source/solution.tex` | Editable, self-contained LaTeX source. |
| `code/verify.py` | Standard-library exact-arithmetic verifier. |
| `certificates/all_subset_certificate.json` | Exact node data, weights, interval endpoints, and all 126 subset records. |
| `certificates/verification_report.txt` | Human-readable output from the verifier. |
| `build_pdf.sh` | Optional PDF rebuilding script. |
| `SOURCES.md` | Original problem and primary-paper source details. |
| `SHA256SUMS` | Integrity hashes of the distributed files. |

## Rebuild the manuscript

A LaTeX installation with `pdflatex` and the packages named in the source is needed only to rebuild the PDF. These include AMS mathematics packages, `geometry`, `lmodern`, `microtype`, `hyperref`, and `enumitem`.

On a POSIX system:

```sh
sh build_pdf.sh
```

Equivalently, run `pdflatex -interaction=nonstopmode -halt-on-error solution.tex` twice from the `source/` directory, then copy the resulting PDF to the package root. Rebuilt PDF bytes can differ because of timestamps or LaTeX versions. The supplied SHA-256 manifest describes the files as distributed, before regeneration.

## Verification scope

The analytic proof of the finite counterexample is independent of the enumeration. The executable certificate additionally proves optimality and checks every subset for that finite witness. The general amplification theorem is proved analytically, not certified by the Python enumeration. This is not a proof-assistant formalization or an externally peer-reviewed manuscript.

No claim is made that nine is the smallest possible counterexample size, that the demonstrated dimension-growth exponent is optimal, or that an exhaustive bibliographic priority search has been completed. Those qualifications do not affect the counterexample to the displayed universal statement.
