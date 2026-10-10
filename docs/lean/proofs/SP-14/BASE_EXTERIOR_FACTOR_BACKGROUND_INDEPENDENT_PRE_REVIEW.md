# SP-14 exterior boundary factor and finite background: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen mathematical contract for implementation of the two narrow gates. This approves no analytic norm bound or full counterexample claim.

| Reviewed input | SHA-256 |
| --- | --- |
| Exact contract `BASE_EXTERIOR_FACTOR_BACKGROUND_PRE_REVIEW.md` | `351bd895ab5f59accae68ab8f566677045a4fe4f119214356b77f8b5a4518b6a` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `NLA.Statements.SP14` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Reviewed base coefficients | `63dcd98bb3a45e77b2b0fd2644d444f9cfe866fb9dae5535d1b7cd1f73081bf4` |
| Reviewed coefficient summability | `1da659ff573ddee8d598d32150fec45f7ae5d5eb023c2a9277a0500547ad9892` |
| Reviewed exterior series | `8e19c9af8809fc44414b90696a089d32417934475adc95f58aafa6db5b83dd0d` |
| Reviewed boundary square | `93b81c168bf831439928020397bb14985f9fe26de2060e50c2c55a535c9e6239` |

I compared the contract with the source's displayed `a(z)=zg(z²)`, exterior branch `g₀(s)=sqrt(1+s⁻¹)`, strict-sign finite `P₋,P₊` each vanishing at `−1`, and `h(s)=sg(s)²−1`. The audited `baseCoeff` series has the source's normalized exterior branch: its constant term is exactly one and the binomial Cauchy product is exactly `1+X`. On the unit circle, every negative power exists and has modulus one. Absolute coefficient summability therefore permits the circle series and its Cauchy product without excluding the zero of the factor. `g₀(-1)^2=0` forces `g₀(-1)=0`; this uses no division or sign choice. Substituting `s=z²` gives termwise `z(z²)^(-n)=z^(1−2n)`, with no missing coefficient or conjugation.

The finite real Laurent formulas start at powers `−1` and `+1`, with exact zero in the empty-vector cases. Expanding `(g₀+P)²` and using `g₀²=1+s⁻¹` gives `h−s=2s g₀P+sP²` exactly: `s(1+s⁻¹)−1=s`. The symbol identity similarly follows by distributing `z` and the source-locked base-symbol factor. Separate premises `P₋(-1)=0` and `P₊(-1)=0` give the source's `g(-1)=0` and `h(-1)=-1`. For the proposed two-term check, `(-1)^(-1)+(-1)^(-2)=−1+1=0` and `(-1)+(-1)^2=0`, so the contact holds for every real `t,r`. The statements include `u=0`, `v=0`, and `u=v=0` without a hidden nonempty assumption.

The implementation should retain these exact coefficients, exponents, and `Circle`/`ℂ` coercions, and prove continuity of all five boundary functions. The source's exterior holomorphy, Wiener smallness, Sobolev inverse estimates, nonlinear packet construction, and final negative Target remain open and may not be inferred from this algebraic gate. Freeze each Lean module unimported for a separate source/signature/kernel audit.
