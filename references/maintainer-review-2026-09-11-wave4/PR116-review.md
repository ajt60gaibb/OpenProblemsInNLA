# Independent mathematical review of PR 116

Reviewed head: 7d34abbd7d8fb12a37fea28ba68875c54780a5ed.
Verdict: PASS mathematical proof and original target match. Required CI and integration remain separate gates.

Read the complete proof and reconstructed its steps. The homotopy has strictly negative imaginary part on the unit circle, so the argument principle gives exactly n interior determinant zeros, including singular leading/trailing coefficients. The factorization is exact; the stabilizing n-by-n factor exhausts these zeros, and Rouche excludes interior zeros of its limiting complement. Palindromic coefficient symmetry gives degree plus zero-root multiplicity 2n, hence n-m interior roots. Simplicity of the 2m boundary roots forces m distinct simple selected eigenvalues and bounded powers of S. The limiting equation yields H=S*HS. For a selected boundary eigenvector, the Hermitian pencil determinant has a simple root, so its adjugate gives a nonzero derivative 2 v*Hv. The Stein identity makes distinct boundary vectors H-orthogonal, establishing rank at least m. All stable generalized eigenspaces lie in ker H by iteration and bounded powers, giving rank at most m. None of the steps assumes real coefficients, positive H, invertible C/D, or semisimplicity strictly inside the disk.

Canonical Problem statement is byte-identical to main at aaa88c4; all 203 ID/path mappings unchanged. Submitted packaging checker passed; fresh validator and all 17 safeguard tests passed; catalog regeneration clean. Read-only PDF QA by an independent agent inspected all six pages and checked all 164 mathematical expressions against Markdown/TeX. See [the PDF/source check](PR116-pdf-qa.md).

Primary source checked: https://uregina.ca/~chguo/JCAM_GuoKuoLin.pdf, Theorem 5 and subsequent equality conjecture. It has exactly the same complex-coefficient setting and conditional nonsingular limit. Its upper-bound proof supports the original scope, not an assumed equality.
