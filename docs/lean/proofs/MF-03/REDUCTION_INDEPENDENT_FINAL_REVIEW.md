# MF-03 generic reduction: independent Lean source review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `Reduction.lean` as a kernel-checked proof of the exact conditional reduction contract. It turns a **supplied** normalized Padé pair of order `m` into a reduced normalized pair representing the same rational function. It does not construct normalized pairs at all orders, prove a disk bound, or prove the full MF-03 `Target`.

The public theorem `normalized_exists_reduced` has precisely the reviewed signature: from `NormalizedPadeRepresentation m P Q`, it returns polynomials `Pᵣ,Qᵣ` with `ReducedPadeRepresentation m Pᵣ Qᵣ` and the cross-product identity `Pᵣ * Q = P * Qᵣ`. There is no positivity restriction on `m` and no hidden witness or reducedness premise. The cross product preserves the rational function without division at possible roots.

The proof takes `D=gcd(P,Q)`, `P₁=P/D`, and `Q₁=Q/D`. The original normalization `Q(0)=1` proves `Q≠0`; the exact `j=0` Padé equation proves `P.coeff 0=1`, hence `P≠0`. Gcd divisibility and nonzero `D` give `D P₁=P` and `D Q₁=Q`. Evaluating the latter at zero gives `c Q₁(0)=1` for `c=D(0)`, so `c≠0`. The output is `Pᵣ=(C c)P₁`, `Qᵣ=(C c)Q₁`; multiplying **both** quotients by this unit gives `Qᵣ(0)=1`. Divisor degree bounds and constant multiplication preserve both degree limits `≤m`. The quotient-gcd coprimeness theorem, followed by invariance under multiplication of both arguments by the unit `C c`, proves `IsCoprime Pᵣ Qᵣ`. The displayed factorizations and commutativity give the exact cross-product conclusion.

For the coefficient conditions, the private `waveSeries` has coefficient `1/(2j)!`, exactly the frozen series. The original Padé equations are converted to equality of coefficients of `Q·waveSeries` and `P` for **every `j≤2m`**, including `j=2m`. The quotient factorization makes the equalities share `D`. The private strong-induction lemma cancels a formal series factor with nonzero constant coefficient: in degree `j`, all product terms using a lower coefficient of the unknown difference vanish by induction, leaving its degree-`j` coefficient times `D.coeff 0≠0`. This yields the quotient Padé equations through the same endpoint. Scaling both quotient polynomials by `c` preserves each linear equation. No analytic power-series convergence is assumed or needed.

I ran the pinned `lake build NLA.Proofs.MF03.Reduction` and a separate imported audit checking the elaborated theorem signature, `#assert_trust kernel`, and `#print axioms`. Both passed under Lean 4.33.1; the transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/MF03/Reduction.lean`** | **`0e58cdba5a4302aa025201e73143a4c3056f33fc43c618da6bf4aa0095da89cb`** |
| Frozen `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `REDUCTION_PRE_REVIEW.md` | `331d29fb2c700a53dee761fe27adcda91bcb383c08481d5da4557800fd208d37` |
| `REDUCTION_INDEPENDENT_PRE_REVIEW.md` | `e763fcc1402da6e05b2c23ebe0e937f76a58c263ed081ae6d360020e493b1cac` |
| Independent `/private/tmp/mf03-reduction-independent-audit.lean` | `87f201917db45e85defc00402606505968e23baadcd7a4d0b4e71164dcbded24` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed theorem, target, or pre-review bytes reopen the corresponding review.
