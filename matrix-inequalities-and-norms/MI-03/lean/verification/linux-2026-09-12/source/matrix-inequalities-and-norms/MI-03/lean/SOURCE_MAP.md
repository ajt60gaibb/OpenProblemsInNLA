# MI-03 source correspondence

This is a statement-only formalization of the complete canonical MI-03 target at `c0601d8825e9f9e744212c62e6a43fefc1c60a22`. [Source hashes](reviews/source-hashes.json) bind the original canonical README, TeX/PDF, complete solution Markdown/TeX/PDF, original authored proof and retained independent informal review. No original file is changed.

Mathematical proof: Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI assistance and no contact email. Bourin and Lee retain original conjecture and previous-bound attribution. The formal proof will establish the needed upper bound itself; no literature inequality is assumed.

| Canonical/source object | Actual formal object and obligation |
| --- | --- |
| Complex n by n matrix | `Matrix (Fin n) (Fin n) ℂ`, with n≥1 in the universal property. |
| Positive modulus `(X*X)^(1/2)` | `matrixModulus X = CFC.sqrt (X.conjTranspose * X)`; PSD, actual square identity and operator-norm identity must be proved. |
| Operator norm | Norm of the actual complex Euclidean continuous linear map `Matrix.toEuclideanCLM X`. |
| Original matrix inequality | Actual `PosSemidef` of `cI+Σ|A_j|−|Σ A_j|`. |
| Admissible c≥0 for every n and every contraction tuple | `AdmissibleConstant k c`, without additional field, spectrum or commutation restrictions. |
| Infimum c_k | Actual real `sInf (admissibleConstants k)`; IsLeast and its membership/lower-bound conditions are required before infimum equality. |
| Source upper proof and explicit positive decomposition | Exact matrix identity in `positive_decomposition`, followed by complete `universal_upper_bound`. Half the ordered pair sum equals the original unordered pair sum. |
| Source root ω and every j=0,…,k−1 | Actual complex exponential and powers indexed by `Fin k`; generic unit norm and vanishing geometric sum, not a supplied phase array. |
| v_j and e1 v_j* | Actual complex vectors and conjugated outer products in dimension two, with actual Euclidean norms. |
| Exact modulus/sum identities | All matrix equalities and operator-norm-one facts are conclusions of `sharpness_witness`. |
| Forced lower bound c≥k/4 | Specialization of the complete admissibility property to the actual witness and PSD positivity at e1. |
| Target for every odd k≥3 | `OddContractionConjecture`; proved from the stronger IsLeast/infimum theorem for every k≥2. |

The proof architecture preserves the manuscript's exact argument. The ordered-pair variance is a representational simplification of the same finite identity. The use of ordinary `sInf` requires, rather than bypasses, actual attainment and lower-bound evidence. The formalization excludes the manuscript's additional Hermitian three-by-three witness and any rank-classification theorem, while fully covering its original odd-summand question.

The campaign studied [Schiffer at 2938e277](https://github.com/jaumededios/Schiffer/tree/2938e277969c329caf154e48a3d8823f3635c7f1) for statement/analytic-proof separation, and [Forsythe at 8d1b0c05](https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof) for explicit kernel-mode LeanCert and Comparator organization. No mathematical result from either project is assumed. Shared checker reuse and licenses are documented in the repository. Existing campaign matrix-modulus/norm helpers may be adapted with credit; this package will not depend on another problem's unmerged source tree.

The relevant Tau Ceti Review rubrics are pinned at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b` and applied through the repository protocol. This is not official Tau Ceti endorsement. Statement approvals, actual proof, two independent final reviews and real Linux verification are distinct stages. A mere successful build, decorative LeanCert call or one scalar sharpness example is insufficient for the complete canonical target.
