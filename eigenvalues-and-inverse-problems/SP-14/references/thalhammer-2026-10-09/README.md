# SP-14 — a continuous counterexample to Widom's canonical distribution conjecture

**Author:** Clemens Thalhammer, Seminar for Applied Mathematics, ETH Zurich.

**Date:** 9 October 2026.

**Claim:** negative resolution of the complete original target of
[SP-14](../../README.md). [Standalone proof (PDF)](counterexample.pdf) ·
[LaTeX source](counterexample.tex). The main result is **Theorem 6.1**.

## What is proved

There is a continuous complex symbol $`a`$ on $`\mathbb T`$ with neither an
inner nor an outer annular analytic extension, and an increasing sequence
$`n_j`$, such that $`T_{n_j}(a)`$ has both $`1`$ and $`-1`$ as eigenvalues of
algebraic multiplicity at least $`\lfloor\theta(n_j-1)/2\rfloor`$ with
$`\theta=2^{-10000}`$. Both points lie outside $`a(\mathbb T)`$. For the
continuous compactly supported test function
$`\Phi(w)=\max\{0,\,1-8|w-1|\}`$ the canonical integral is $`0`$ while the
empirical eigenvalue integrals are at least $`\theta/2`$ along $`n_j`$. The
displayed universal limit therefore fails for this $`a`$ and this $`\Phi`$.

The symbol has the form $`a(z)=z\,g(z^2)`$ with
$`g(s)=\sqrt{1+s^{-1}}+P_-(s)+P_+(s)`$. The base symbol
$`a_0(z)=\sqrt{z^2+1}`$ traces the lemniscate $`|w^2-1|=1`$, a figure-eight
through the origin, and $`T_{2m+1}(a_0)`$ has characteristic polynomial
$`w(w^2-1)^m`$ exactly. Positive packets $`\tau_j s^{m_{j-1}}(1+s)`$ with
$`\tau_j=\kappa\,2^{-\lceil\sqrt{2m_{j-1}+1}\rceil}`$ destroy the outer
extension; finitely many corrections of the negative coefficients
$`g_{-m_j},\dots,g_{-5m_j/8-1}`$, each followed by an invisible endpoint-restoring
packet, recreate the factor $`(w^2-1)^{\lfloor\theta m_j\rfloor}`$ in the
characteristic polynomial of $`T_{2m_j+1}(a)`$; the untouched coefficients
$`g_{-3m_j}=\binom{1/2}{3m_j}`$ destroy the inner extension. Later stages change
no entry of an earlier selected section, so the factor persists in the final
symbol. All parameters are explicit, and every correction is fixed by a
deterministic finite certificate search; no computational efficiency is claimed.

## Comparison with the original target

The retained statement quantifies over every continuous symbol with both
extensions absent and over every continuous compactly supported test function,
with eigenvalues counted by algebraic multiplicity. The proof exhibits one such
symbol and one such test function for which the limit is not the canonical
value, which refutes the universal statement. The symbol's range is not a
Jordan curve, so Widom's Jordan-curve theorem, Tilli's theorem and the
Jordan-range subsequence result recorded on the canonical page on 13 September
2026 are untouched and consistent with this counterexample. The two formulations
of the conjecture checked against primary and secondary sources (Bogoya,
Böttcher and Grudsky 2012, §1; Basor and Morrison; arXiv:1807.01441) carry no
Jordan-curve hypothesis. Widom's 1990 text itself was not consulted.

## Verification level

[Independent informal AI-agent review](verification/independent-review-2026-10-09.md),
9 October 2026, by Claude (Anthropic, model Fable 5.1), in a session separate
from those that produced the argument. The review verified every finite
identity exactly, reproduced the construction end to end at a small order in
60-digit arithmetic, confirmed the two central analytic estimates numerically up
to order 8192, and audited the logical chain and both external citations. It
did not recompute the explicit constant ledger and did not re-prove the
two-level isomorphism and far-factor derivative propositions line by line.
This is not external human peer review, and no Lean verification was performed.

**AI-assistance disclosure.** The argument was developed with substantial AI
assistance in ChatGPT (OpenAI) sessions directed by the author, who takes
responsibility for the mathematics. The author's own adversarial self-audit and
research notes are not part of this package.

## Sources and publication edits

`counterexample.tex` is the author's source without modification
(SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`).
`counterexample.pdf` was built from it with
`pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error counterexample.tex`,
run twice (TeX Live 2023). Rebuilding changes PDF metadata, so the PDF hash is
not binding.

## Reproduction of the independent checks

`verification/scripts/` holds the reviewer's standalone scripts (Python 3,
NumPy, SciPy, mpmath; no submitted code is imported). Run from that directory:

```sh
python3 finite_algebra.py   # Prop. 2.1 identities, Lemma 3.2 convolution identity, ||H-I|| bound
python3 exact_small.py      # 60-digit end-to-end check at m=32, h=2
python3 conformal.py        # forcing decay and Jacobian conditioning in both coordinates, m<=2048
python3 nested.py           # two-stage nested background and stage-2 solve
python3 stability.py        # pencil stability bounds, Gohberg-Semencul identity, tail identity
python3 fastjac.py          # fixed high-degree background up to m=4096
python3 scaled.py           # degree-uniformity at fixed weighted Wiener norm
python3 highdeg.py          # high-degree negative backgrounds
python3 profile.py          # k-profile of the forcing jets
```

The largest runs need a few gigabytes of memory and several minutes. Finite
numerical diagnostics support but do not replace the analytic argument.
