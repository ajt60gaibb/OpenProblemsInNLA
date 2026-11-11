# Independent TR-26 pre-proof approval

**APPROVE the frozen three endpoint signatures and faithful proposed mathematical route.** Independent non-author reviewer `/root/inventory`, 2026-10-26. I read the complete credited manuscript Markdown, canonical original and exact specification, live/frozen Lean definitions, contract and all three signatures. A delegated independent non-author [statement/math audit](PRE_REVIEW_CHILD_INVENTORY.md) additionally checked the complete TeX source and exceptional-case arguments. I authored no TR-26 proof, statement or contract. This approval proves no target and claims no Linux or Comparator acceptance. Coordinator approval and the separately assigned second independent review remain separate gates before implementation.

The packet is now immutable at commit `94dd4adb910c5b5e1114528c1c4d9f272347743a`, path `docs/lean/proofs/TR-26/campaign-2026-10-26/preproof/`. All 24 frozen originals and all six contract/scaffold inputs match that commit and the final lock. The originals also match both published bases `5487945e5a72abd952b0c89915915de8cc9b3e65` and `01ed3c64648d2d8350ba80c4018894b6d785d2c9`. All 217 IDs/paths remain fixed; TR-26 remains `tensor-computations/TR-26/README.md`. Core SHA256 bindings:

| Input | SHA256 |
| --- | --- |
| INPUT_LOCK | `59314bd19a35f47dadd9a672517d4f9053682b4454b79c571cb915231342a91c` |
| Challenge | `122ad60aaddf59e91dacd627637cf7237b8614d83b6d2eead381a76a698d7aba` |
| CONTRACT | `26625969b0c33b85d5e6dcb59dd2c3c9f9ca1389fcc92f4b3f1f1facb81d56a0` |
| Live statement | `e0b38f44232ea35418e8afb9bcd0c1df0e2dd51642cda71e8bf62564a130095f` |
| Frozen Reviewed statement | `e1700dde28c3679f126eaae1ea7cb16e979a18e94f1e77d198996f0f6ede6820` |
| Complete manuscript Markdown | `4a96398678689820dffd81522991fa4178062789afd657acc73194f0852185f8` |
| Complete manuscript TeX | `bfb2f0fce6d67649dc8faca5965f79f898c4cb040645e721df5095446cd89b8e` |

`nonisotropic_degree` has exactly `∀ d, 2 ≤ d → HasReducedDegree d (6*(d-1)) (NonisotropicClosure d)`; `isotropic_degree` has exactly `∀ d, 2 ≤ d → HasReducedDegree d (2*d) (IsotropicImage d)`. These are precisely the two conjuncts of the unchanged Target. `target` itself has literal closed type `NLA.Statements.TR26.Target`. No endpoint assumes genericity, a factorization certificate, denominator simplicity, conormal equivalence, a chosen equation or any of the desired degree conclusions.

The meanings preserve the fixed unweighted complex Veronese embedding, complex bilinear pairing without conjugation, both projective parameter charts and all nonzero symmetric matrices in independent upper-triangle coordinates. The tested ordinary derivatives correctly vanish at zero exponents; both parameter directions express curve criticality rather than ambient stationarity. The extra representative scalar and nonzero cone conditions correctly retain projective representatives.

The incidence is the common-zero closure of the **entire** polynomial vanishing ideal. The Jacobian span uses the curve-variable partials of every polynomial in that ideal. On the incidence, multiplication by polynomial coefficients does not change the generated evaluated conormal span; this is the correct generator-independent rank meaning. The formal proof must establish the actual local ideal and conormal/rank bridge. A convenient Wronskian equation alone does not establish that bridge. The homogeneous radial direction and both charts must remain included. The exact isotropic image has no new closure; the nonisotropic image has its separately required closure. `HasReducedDegree` demands a nonzero squarefree homogeneous polynomial with the prescribed degree and exact zero-set equality for every nonzero matrix. With `d≥2`, the requested positive degrees exclude a constant/vacuous hypersurface witness.

The complete manuscript supplies a sound route. Antidiagonal coefficients make the numerator map genuinely surjective over ℂ, with off-diagonal coefficient 2 invertible. The fixed denominator has exactly 2d simple finite nonzero roots because `(t²-1)D=t^(2d+2)-1`, with neither coordinate endpoint a zero. Its fixed binary Wronskian has degree 4d-2 even when an individual affine specialization loses leading terms. Thus a variable-`natDegree` affine discriminant is insufficient: fixed-degree binary discriminant and infinity behavior must be proved, not assumed.

At denominator roots the actual incidence and ramification conditions give precisely the 2d distinct evaluation hyperplanes. Off those roots, jet interpolation gives the irreducible hypersurface and separates it from every isotropic component. For `d≥3`, the higher jet conditions bound the triple-root/two-double-root exceptional loci. At `d=2`, `N=t³`, `D=1+t²+t⁴` gives `F=t²(3+t²-t⁴)`, with exactly one nonisotropic double root, four other simple roots and no infinity root. This supplies the missing small-degree generic-pattern witness without extrapolating a computation.

The discriminant's nonzero differential at a unique double root restricts to a nonzero functional on the actual numerator family. That is the necessary multiplicity-one step; merely replacing an eliminant by its radical and keeping its degree would be invalid. The fixed discriminant degree 8d-6 minus the squarefree isotropic degree 2d then gives 6(d-1). Zero numerators, all numerators proportional to the denominator and every nonzero matrix in the numerator-map kernel remain included. The surjective affine linear map/splitting, rather than an undefined projective rational map at kernel points, is the appropriate pullback route. No stronger irreducibility statement is imposed on the endpoints.

I independently executed the locked `check_scaffold.py` in fresh `/private/tmp/nla-tr26-inventory-boundary-59314`, with fresh retained output `verification/inventory-preproof/`. The official Lean 4.33.1 runtime at commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` compiled Infrastructure, live TR26, Reviewed TR26, Challenge and a live/frozen Target equality proved by `rfl`. The separate negative consumer actually rejected **all three** reference placeholders under LeanCert kernel trust, each with `sorryAx`; its required exit was 1. All ten dependency Git revisions equal the frozen manifest and their tracked sources are clean. This is boundary elaboration and rejection evidence, not a TR-26 proof.

The JSON records **131/131 passing checks**, all inputs, immutable copy bindings, six command outcomes, compiler version, dependency pins and log hashes. Two preliminary reviewer receipt-format predicates were corrected (Darwin version suffix and `sorryAx` label/value formatting); the unchanged actual compiler/log evidence is preserved, together with the preliminary diagnostic. No statement, theorem or proof was changed to make a check pass.

Reproduce the fresh boundary check with the locked script:

```bash
python3 check_scaffold.py --packet /path/to/preproof \
  --lean /path/to/lean-4.33.1/bin/lean --packages /path/to/pinned/.lake/packages \
  --build /tmp/new-tr26-boundary --output /tmp/new-tr26-boundary-logs
```

Both output directories must be fresh. All six source/consumer files used by the independent run remain available in the fresh build directory; generated identity/rejection sources and raw logs are retained with the receipt. Future full-ideal, fixed-degree discriminant, multiplicity and exact-image proofs remain substantial obligations and require separate complete-source/kernel/Comparator reviews. Preserve Matthew J. Colbrook's mathematical credit and the explicit AI-agent review limitations.
