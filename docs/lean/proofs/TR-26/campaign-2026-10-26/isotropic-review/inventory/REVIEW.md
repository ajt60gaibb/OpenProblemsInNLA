# Independent TR-26 literal isotropic endpoint review

**APPROVE `NLA.Proofs.TR26.isotropic_degree` at immutable commit `4692336f0e1a50d5e261bba68277875da30fba51`.** Independent non-author reviewer `/root/inventory`, 2026-10-26. I authored no TR-26 proof, statement, contract or canonical package and did not rely on the other reviewer's approval. The literal raw full-ideal isotropic endpoint is proved for every `d≥2`, with no new hypotheses. **The nonisotropic endpoint and complete TR-26 Target remain unproved; canonical status remains Solved. No Linux or Comparator acceptance is claimed.**

I revisited the unchanged canonical original, complete credited manuscript, exact specification, frozen three-endpoint contract and my prior pre-proof approval, then read the 33 immutable authored support/proof modules. The checkpoint SHA256 is `310cdbff42c1303419de04ff882ab549d8163cf26ccb7b58a4beb5e528530ba4`. The exact endpoint source `IsotropicDegree.lean` has SHA256 `507bbb439ed82d0c87144de91a8f76d611ddb14bbd24d504a9544b351474fd25`. Its outer type is precisely the preapproved signature:

```lean
theorem isotropic_degree (d : ℕ) (hd : 2 ≤ d) :
    HasReducedDegree d (2*d) (IsotropicImage d)
```

Both definitions above are the original live definitions, not replacements. `HasReducedDegree` still requires an actual nonzero squarefree homogeneous equation of degree 2d with exact zero-set equivalence for every nonzero original matrix. `IsotropicImage` is still the **raw projection** of the original ramification locus defined using the span of derivatives of **every polynomial** in the full incidence vanishing ideal. No new closure, selected-equation Jacobian, genericity premise, factorization certificate or oracle is substituted.

## Mathematical assessment

The degree witness is the actual product of numerator-evaluation linear polynomials at the roots of the fixed denominator. `Denominator.lean` proves monicity, degree 2d and separability using `(X²-1)D=X^(2d+2)-1`; algebraic closure then gives exactly 2d distinct roots and nonzero derivative at each root. The upper-triangle numerator coordinate map is concretely surjective, with diagonal coefficient 1 and off-diagonal coefficient 2, whose inverse is 1/2. This is the actual unweighted complex bilinear model, without conjugation or a changed embedding.

`IsotropicFactor.lean` proves that each numerator-evaluation polynomial is nonzero, homogeneous of degree 1 and irreducible. Distinct roots give nonassociated factors: a genuine matrix numerator `X-r` vanishes at one root and not the other. The product is therefore squarefree, nonzero, homogeneous of degree 2d, and has actual total degree 2d. Its evaluated zero set is precisely existence of a denominator root at which the actual numerator vanishes. No multiplicity-counted discriminant degree is used to infer this reduced degree.

For the inclusion from the **raw image** to that zero set, `IsotropicChartCover.lean` proves that every actual isotropic curve point has first projective coordinate nonzero. The missing chart endpoint is not silently discarded: the binary denominator at `(0,1)` is proved to be 1, and scaling by a nonzero representative preserves nonvanishing there. Consequently every isotropic point can be written in the actual chart `z_i=c t^i`, with `c≠0` and `D(t)=0`.

`CriticalEquation.lean` constructs a global polynomial in the original incidence coordinates from the binary Wronskian whose coefficients remain the actual symmetric-matrix variables. It proves this polynomial belongs to the full open-incidence vanishing ideal by the genuine criticality identity and homogeneous scaling. Thus **every** point of the original incidence satisfies the polynomial. In the affine chart it evaluates to `c^(4d-2) W_H(t)`. Since `c≠0`, incidence gives `W_H(t)=0`; since `D(t)=0` and `D'(t)≠0`, the identity `W=N'D-ND'` gives `N_H(t)=0`. This direction uses an actual member of the full ideal and does not pretend the chosen equation generates the entire ideal.

The converse includes the substantive full-ideal rank argument. A common denominator/numerator root makes both Wronskian homogeneous partials vanish, hence its affine value and derivative vanish. `WronskianLinear.lean` and `WronskianCharts.lean` prove that the critical polynomial is linear in the original matrix coordinates and has a nonzero coordinate pivot at every chart point. At denominator roots the pivot is obtained from a matrix with numerator 1; away from them, from numerator `X-t`. These pivots are proved from actual numerator surjectivity and denominator simplicity, not assumed on the endpoint.

`LinearCriticalGraph.lean` then constructs the genuine local parameter curve

`η(s)=H−W_H(s)/L_j(s) e_j`.

Near a nonzero pivot this curve stays critical; at a root it equals the original H, and at a double root its matrix velocity is zero. Continuity keeps H nonzero nearby. `ChartIncidence.lean` tests **every polynomial** in the original full vanishing ideal along `(ζ(s),η(s))`, outside only the finite roots of the actual nonzero denominator. The analytic polynomial-exclusion lemmas extend those zero identities to a neighborhood and differentiate them. Every full-ideal curve-gradient therefore annihilates the genuine chart velocity while holding the matrix velocity zero. Separately, `IncidenceScaling.lean` proves radial annihilation for arbitrary full-ideal polynomials by an actual pullback/scaling argument, without assuming each polynomial homogeneous.

The radial vector and chart velocity are proved independent, and the complex **bilinear** coordinate pairing is proved nondegenerate. The linear-algebra lemma gives `finrank(JacobianSpace)+2≤d+1`, hence the exact rank threshold `≤d−1`. The resulting pair lies in the original incidence and original ramification locus, and its denominator is zero. This establishes membership in the raw `IsotropicImage`, completing the exact zero-set equivalence for every nonzero matrix.

The generic `LocalConormal` generator lemma retains an explicit localization hypothesis, but this hypothesis is **not** imported as an unproved premise of the endpoint. The direct analytic annihilation proof discharges the needed rank upper bound instead. This is a valid concrete route within the preapproved boundary; it avoids neither the full ideal nor the raw projected set. `CurveNormalRank` is additional reviewed support and is not needed in the isotropic endpoint's 32 authored-module import closure.

The proof covers `d=2`, all nonzero representative scalars, arbitrary H, matrices in the numerator-map kernel, zero numerators and numerators proportional to D. Their Wronskians are genuinely zero, and the same proven pivots/local-curve argument works. No assumption that H or its numerator is generic/nonconstant is introduced. The first-chart reduction is justified specifically for isotropic points; this review does not claim that the same reduction resolves the nonisotropic point at infinity.

The additional fixed-discriminant/resultant support is concrete: fixed coefficient sizes, both homogeneous partials, explicit infinity cases, specialization and a universal Fermat nonzero witness are proved. Family homogeneity and isotropic-factor divisibility remain their stated support results; they do not establish the family discriminant's reduced nonisotropic degree or a full Target proof. This review makes no such promotion.

## Independent verification and preservation

The portable static auditor passes **164/164 checks**. It binds all 33 source hashes, the exact preapproved header, explicit kernel mode, absence of admission/custom-axiom/unsafe/native code and reference imports, and all 24 original frozen inputs. The unchanged 217-entry registry and original canonical README/path/Target are preserved. The immutable pre-proof lock remains `59314bd19a35f47dadd9a672517d4f9053682b4454b79c571cb915231342a91c`; Challenge remains `122ad60aaddf59e91dacd627637cf7237b8614d83b6d2eead381a76a698d7aba`.

I independently compiled **36 frozen sources** into my own fresh output objects: all 33 authored modules plus Infrastructure, live TR26 and Reviewed TR26. The exact endpoint consumer and live/frozen Target equality by `rfl` also compile. A generated consumer actually checks **218 public theorem constants** for theorem kind, LeanCert kernel trust and transitive axioms. All 218 use only subsets of `propext`, `Classical.choice`, `Quot.sound`; the selected isotropic endpoint uses exactly those three. The Source/Target definitions and identity certificate are not counted as Target proofs.

Meaningful independent controls actually reject all three exact reference placeholders with `sorryAx`; reject an exact-typed counterfeit isotropic theorem depending on an injected custom axiom; and reject a definition alias when checked as a proved theorem constant. The replay records **41 commands and 126 passing verification checks**, with positive and expected negative exit statuses and raw logs preserved. No failed authored proof was repaired by this reviewer. The initial reviewer setup attempt omitted bare `Lean` from its external-import allowlist and ran no compiler command; its original driver/diagnostic is preserved under `attempts/setup-bare-Lean/`. The corrected driver simply recognizes the pinned core `Lean` import.

The actual runtime is official Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` on macOS. All ten dependency Git heads match the frozen manifest and their tracked sources are clean, including Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. Runtime binary hash, script hashes, exact command arguments, source snapshots, logs and dependency records are retained in `replay-v2/result.json`. Author acceptance records were inspected only as author evidence; this fresh replay uses its own source/object/output directories.

Reproduce the immutable static audit and the fresh pinned replay using the sibling scripts:

```bash
python3 audit_source.py --repo /path/to/OpenProblemsInNLA --output /tmp/tr26-static
python3 reproduce.py --repo /path/to/OpenProblemsInNLA \
  --lean /path/to/lean-4.33.1/bin/lean --packages /path/to/pinned/.lake/packages \
  --build /tmp/new-tr26-build --output /tmp/new-tr26-replay
```

Replay build/output directories must be fresh. Only reviewer outputs are written. Mathematical credit remains with Matthew J. Colbrook; formalization and independent reviews are AI-agent work, not external human peer review. Canonical partial-package review and authentic Linux/Comparator acceptance remain separate later gates.
