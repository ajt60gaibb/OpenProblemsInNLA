# TR-14 apolar chart transport: independent mathematical pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen contract for Lean implementation. It is a partial bridge and does not establish rank preservation or `NLA.Statements.TR14.Target`.

| Reviewed input | SHA-256 |
| --- | --- |
| `GL2_APOLAR_TRANSPORT_PRE_REVIEW.md` | `10e61abda0aa135eff2d561a43b918b25630867ba26e92bb83bd5d2fcc581f40` |
| Canonical `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Audited `ApolarMinimal.lean` | `0e98ae3b414d2130bebe7470a25c7c8b3e422225b5581ae4b93d036f39f520d9` |
| Audited `GL2Homogeneous.lean` | `5d91423c625d687c034b3df7cd14b1a652a707edc4ee436e36d44521baa0f4b7` |

The proposed `form_d` maps the entire `Fin(d+1)` coefficient vector to the homogeneous polynomial `Σ_i g_i X^(d-i)Y^i`. Every two-variable monomial of homogeneous degree `d` has a unique exponent pair `(d-i,i)` for `0≤i≤d`; this makes the monomials a complete linearly independent basis, including the sole constant at `d=0`. The contract correctly requires both inverse identities before using `form_d` to translate an arbitrary test form. A map defined only on monomials, or an injective map without spanning, would leave a gap.

The moment functional `L_h(P)=Σ_j h_j coeff_D(P)_j` is the correct unweighted dual convention for the canonical source. In particular `L_h(X^(D-j)Y^j)=h_j`, and the monomial basis yields the converse reconstruction of every dual functional. The binomial coefficients in the source's associated form `F(x,y)` do not enter this pairing. The condition `h=0 ↔ L_h=0` follows from the two coordinate inverses, without a nonzero-moment premise.

For `d≤D`, put `e=D-d`. Multiplying `X^(d-i)Y^i` by `X^(e-j)Y^j` yields `X^(D-(i+j))Y^(i+j)` because both exponent sums are exact. Thus testing the product against `L_h` gives `h_(i+j)` with no combinatorial factor. Expansion of a general test form `Q` gives the forward implication from every equation `Σ_i g_i h_(i+j)=0`; testing each monomial `Q` gives the reverse implication and retains the endpoints `j=0,e`. The same argument works for `d=0`, `d=D`, and `D=0`, so no restriction from the main theorem's `m≥3,n≥2` should be introduced into this algebraic bridge.

The transported moment vector is the coordinate vector of `L_h ∘ φ_D⁻¹`; the transported apolar form is the coefficient vector of `φ_d G`. The already audited multiplication and inverse-dual pairing imply `L_(h^z)((φ_dG)(φ_eQ))=L_h(GQ)` for every split. Since `φ_e` is surjective and has an inverse, vanishing for every old `Q` is equivalent to vanishing for every transformed `Q'`; the reverse direction uses the same bijection. This proves all-degree apolar equivalence. The coefficient and dual equivalences then preserve zeros, kernel images, and the least nonzero apolar degree for nonzero moments. No chart normalization or width result follows from these algebraic facts alone.

The contract may be implemented in smaller source modules, but each exported theorem must have the exact public signature and endpoint scope above. The source implementation requires a separate frozen-source, escape, imported LeanCert kernel, and transitive-axiom review before aggregate import. Changed contract bytes reopen this pre-review.
