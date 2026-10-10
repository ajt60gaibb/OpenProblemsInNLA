# SP-14 odd-frequency Toeplitz characteristic polynomial: independent pre-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Verdict:** APPROVE the frozen contract for implementation. It is a conditional finite-matrix lemma, not a proof of the SP-14 counterexample or `Target`.

The premise `∀ p : ℤ, FourierCoefficient a (2*p)=0` refers to the **actual frozen interval-integral coefficients**. It suffices to zero both same-parity blocks; no continuity premise is needed after those coefficients have been supplied. Proving that the final continuous infinite symbol has this premise is separate. With `Toeplitz a n i j = FourierCoefficient a (i−j)`, the even-row/odd-column block has frequency `2i−(2j+1)` and size `(m+1)×m`, exactly `oddB`. The odd-row/even-column block has frequency `(2i+1)−2j` and size `m×(m+1)`, exactly `oddC`. The reviewed `baseParityEquiv m` orders even indices first and odd indices second, so `oddC*oddB` is `m×m`; neither factor may be transposed.

The reviewed rectangular block theorem gives, for unrestricted complex `B,C` and every `m`,

\[
 \operatorname{charpoly}\begin{pmatrix}0&B\\ C&0\end{pmatrix}(w)
 = w\,\operatorname{charpoly}(CB)(w^2).
\]

Reindexing by the parity equivalence preserves the characteristic polynomial. Thus `Q_m(u)=charpoly(oddC*oddB)(u)` yields the claimed `w Q_m(w²)` with no division at `w=0` and no spectral assumption. Defining `R_m(t)=Q_m(t+1)` gives the exact identity `R_m(w²−1)=Q_m(w²)` by polynomial composition. At `m=0`, the lower block is empty, `Q_0=1`, and the odd-support premise makes the actual `1×1` Toeplitz section zero, so both formulas are `w`. At `m=1`, the parity order is `(0,2;1)` and `CB` is `1×1`; directly, the characteristic polynomial is `w(w²−2a_1a_{-1})`, confirming the block orientation.

This contract proves only the source's “no division ambiguity” algebra. It supplies no vanishing jet of `R_m`, selected correction vector, root regularity, positive asymptotic multiplicity at `±1`, final infinite-symbol support, nonextension, or test-function gap. The base exterior symbol still has an outer extension and is not the final counterexample.

| Reviewed input | SHA-256 |
| --- | --- |
| **`ODD_FREQUENCY_TOEPLITZ_CHARPOLY_PRE_REVIEW.md`** | **`55a5674b0f17f283d13f2a9d1b6b1ab1f18aca9faae5b8a21074acf9cc439382`** |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Reviewed `BaseParityBlocks.lean` | `06ef7ef23d4ea068188c011c680c2c4a43ee8ef6d8a0a8c23dfbac943dc4c5f2` |
| Reviewed `BaseOffdiagonalCharpoly.lean` | `c503becdb5f9c1cae1da8724c744ebbdf3937316e5536702eaac865de3b88e33` |

Changed contract or canonical source bytes reopen this review. The eventual Lean theorem needs a separate signature, source, LeanCert kernel, and axiom audit.
