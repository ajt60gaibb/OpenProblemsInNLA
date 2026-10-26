# TR-14 actual binary inverse and separable apolar pencil — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored none of these modules. **APPROVE these exact three new support modules.** They do not yet prove the full TR-14 Target; actual reconstruction into bounded symmetric width and the ordinary lower bound remain separate work.

| Module | SHA-256 |
| --- | --- |
| `TR14BinaryInverse` | `85dc86eaee659fd82a785ab81b1e631cc8347549ecafc64d7db19782d9394bc8` |
| `TR14BinaryPencil` | `c74cd7bf8a1f38b3082650281c828c666e3fbb625409e63d5ab9232bb4c20ca0` |
| `TR14BinaryApolarPencil` | `498f8918ff891ef2d2fa28b4826c5aa1f17493c3607b44351a993d34864dfbd5` |

`TR14BinaryInverse` uses the actual least-apolar quotient unit inverse proved by the existing foundation. The inverse remainder is nonzero and has degree below the positive monic modulus. At a root of the modulus, the quotient evaluation homomorphism sends the unit equation to a nonzero product, so the remainder cannot vanish there; complex algebraic closure converts that to actual coprimality. The unit representation of the moment functional reduces its shifted products to the existing top-remainder functional on lower powers. Thus the precise low-moment annihilation is derived from the existing moment algebra rather than supplied as an independent inverse-polynomial oracle. The nonzero moment vector, monicity, positive bounded degree, actual apolarity and minimality remain explicit local hypotheses.

`TR14BinaryPencil` proves the actual Wronskian is nonzero from coprimality and positive modulus degree. If it vanished, coprimality would force the modulus to divide its nonzero derivative, contradicting the strict degree drop in characteristic zero. The finite exceptional parameter set is explicitly the Wronskian roots' critical values. A pencil common root with its derivative has nonzero modulus evaluation by coprimality and hence forces exactly one forbidden parameter. Choosing outside that finite set and zero proves an actual separable member. For a monic polynomial and lower-degree perturbation, inverse scalar normalization keeps the monic leading coefficient and exact degree. No genericity, discriminant nonvanishing or finite-critical-value premise is assumed.

`TR14BinaryApolarPencil` expands the actual quotient moment functional at every shift whose required index lies in the finite input vector. Its recurrence conversion explicitly retains that finite moment bound. To obtain any requested larger modulus degree it multiplies the actual monic modulus by powers of a linear factor avoiding the nonzero remainder's finite root set; degree, divisibility and coprimality are proved. For degree `D-r+2`, the supplied bound `r ≤ D/2+1` gives the needed degree comparison. The preceding actual pencil supplies a monic separable polynomial. In the quotient, its large multiple vanishes and its remaining scalar multiple is the actual inverse remainder. Every available recurrence shift is strictly below `r-1`, exactly the proved annihilation range. When the output degree is `D+1`, there are no available shifts and the guarded recurrence is correctly vacuous. There is no claim of additional unavailable moments, unproved squarefree existence or already-established decomposition width.

Independent immutable-source verification passed **14 Lean commands**: 13 actual local source modules (these three new modules, eight imported proof foundations, and two statement/infrastructure files) plus a separate consumer. It audits **39 explicit declarations**, including **33 theorem/lemma constants**. Every proof name must have Lean's theorem kind; every explicit declaration passes LeanCert kernel trust and transitive printed axioms. Only the three standard axioms occur. All ten pinned dependency trees and all frozen source bytes passed before/after. Every local object is freshly built in a private output directory, using only pinned cached dependency objects. No campaign project objects are used.

Reproduce from the repository root:

```bash
python3 docs/lean/proofs/TR-14/verification/check-binary-closure.py \
  --top TR14BinaryApolarPencil --evidence-name binary-construction-review-3
```

Exact driver, source/consumer snapshots, hashes, raw logs and result are in [verification/binary-construction-review-3/](verification/binary-construction-review-3/). An initial auditor declaration-parser attempt did not recognize `noncomputable section` in an imported foundation; its failed pre-build result and driver are preserved separately. The corrected parser tracks that real scope and every actual source/consumer build passes. No mathematical source was changed for this audit.

The imported foundations' mathematical fidelity is covered by the separate existing source reviews and the fresh preproof statement approvals. This report supplies fresh runtime/constant evidence for that exact import closure and independent mathematical review of the three newly authored files, not a new review of every retained TR-14 module. It is local macOS Lean4.33.1/LeanCert kernel evidence, not a full Target proof, Linux Comparator receipt or external human peer review.
