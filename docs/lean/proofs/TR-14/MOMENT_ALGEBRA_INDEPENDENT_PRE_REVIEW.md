# TR-14 finite moment algebra: independent pre-proof review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `MOMENT_ALGEBRA_PRE_REVIEW.md` as an exact mathematical and proposed Lean contract for the finite moment-algebra foundation. This is a source review, not a Lean proof of the foundation or `NLA.Statements.TR14.Target`.

I compared the contract with the canonical TR-14 statement, the frozen Lean widths and Hankel index, and `solution.tex` §2, especially Lemma 2.1, its displayed apolar equations, the choice lemma, and the local algebra identities. The zero-based apolar convolution `Σ_{i=0}^d g_i h_{i+j}=0` for every `0≤j≤D−d` matches the homogeneous form convention `G(X,Y)=Σ g_i X^(d−i)Y^i`. The proposed middle matrix uses `floor(D/2)+1` rows and `ceil(D/2)+1` columns with entry `h_{i+j}`, with no conjugation. These bounds include both even and odd `D` and retain every moment through `D=m(n−1)`.

The contract correctly separates the zero tensor from the nonzero minimal-apolar-degree construction. Surjectivity of `HankelIndex` for `m≥3,n≥2` identifies a zero Hankel tensor with `h=0`; width zero is already certified separately. For nonzero `h`, `I₀=0` and the rectangular kernel count gives `1≤r₀≤floor(D/2)+1`. The `r₀=1` endpoint is included. No selected-width `r`, genericity, squarefree-root, or nonzero-catalecticant assumption is added to the final target.

For a monic affine `g` of exact degree `r₀`, the displayed recurrence is precisely the apolar equation whose range `0≤j≤D−r₀` propagates the quotient functional through **all** moments `0,…,D`. The radical argument requires a proper divisor `g'` to yield a smaller apolar recurrence and therefore proves a nondegenerate Frobenius pairing, not merely a nonzero functional. The two degree-bounded polynomial spaces then surject onto the quotient, so the middle catalecticant rank is `r₀`. The contract explicitly requires a proved `GL₂(ℂ)` chart change or coordinate-free substitute before transporting this equality back to arbitrary original `h`; fixing a monic chart as a new hypothesis would weaken the claim.

The source's choice-space dimensions are recorded accurately: one when `D≥2r₀−1`, two when `D=2r₀−2`; the latter is the balanced endpoint and the final rank formula's independence of the chosen minimal apolar form remains a later obligation. The CRT factors preserve whole local multiplicities, each restriction of the functional is Frobenius, the image dimension on a nonempty collection of factors is `min(n,r_J)`, and products of all but one mode span the full quotient since `(m−1)(n−1)≥r₀−1`. These exact statements are the inputs needed by the arbitrary ordinary-decomposition lower bound.

The Lean snippets in the contract are intentionally **API sketches** with dependent-bound ellipses; this approval is of their mathematical meanings and quantifier scope, not a claim that they elaborate unchanged. Each implemented theorem still needs an exact-signature and source-hash audit under LeanCert kernel mode. The full frozen all-width target remains open.

| Reviewed input | SHA-256 |
| --- | --- |
| **`MOMENT_ALGEBRA_PRE_REVIEW.md`** | **`2297de29286de55999709753278dcf84c1b4dd67640f4064baa98ba93165a840`** |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Proof `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |

Changed source bytes reopen this review.
