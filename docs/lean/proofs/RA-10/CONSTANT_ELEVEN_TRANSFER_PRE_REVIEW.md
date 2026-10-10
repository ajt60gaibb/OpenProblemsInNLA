# RA-10 constant-eleven nuclear transfer: exact pre-implementation contract

**Status:** mathematical and signature proposal for independent review. No Lean proof is claimed here. The permanent `RA-10` ID, canonical README, frozen `NLA.Statements.RA10.Target`, and its quantifiers remain unchanged.

## Source lock and exact objective

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `randomized-and-low-rank-approximation/RA-10/solution.tex` | `ec2ae9f759e2df80b022ed5f523d0fecc813e6faa62cbae00271af6c82ccd48f` |
| `references/stepaniants-ra10-2026-09-11/verification/RA-10-independent-review.md` | `c1d6664ea1099671fa2603d99170b11a96512dbdafbfbdf76a22b2cc500bb1ad` |
| `docs/lean/statements/RA-10/NUMERICAL_TARGETS.md` | `9a736152257f91d97f113a7b8b43d286e268a25fa142a97bdd62214387cb85de` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |

The final theorem must prove **exactly** `NLA.Statements.RA10.Target`, with witness `C = 11`. In particular it must prove `NLA.Statements.RA10.TransferBound 11`, not a commuting, strictly positive, gap-separated, or specially chosen eigenbasis variant. The statement quantifies over every `n ≥ 2`, `1 ≤ k < n`, every real PSD pair with every supplied ordered orthonormal eigendecomposition, every `ε ≥ 0`, and every `f : ℝ → ℝ` satisfying the frozen `AdmissibleFunction` predicate. The latter constrains `f` only on `[0,∞)`; values at negative arguments must not become an extra hypothesis. The selected eigenbasis of `Ahat` is used in both its identity-function and `f` truncations, including ties and selected zero eigenvalues. `NuclearNorm` is the sum of the actual `n` singular values of `Matrix.toEuclideanLin`; it cannot be replaced in the public conclusion by an unproved trace surrogate.

## Mathematical spine and proposed Lean gates

All internal zero-based spectral indices below use `i : Fin n`; “top `k`” means `i.val < k`. Internal matrices may be recast as self-adjoint Euclidean operators, but an exact equivalence to the frozen entrywise matrix definitions must be proved before the final theorem.

1. **Spectral/nuclear bridge.** For every frozen `OrderedPSDSpectralDecomposition A a Q`, establish self-adjointness, PSD, orthonormality, ordered nonnegative eigenvalues, and the literal reconstruction. Prove that frozen `FunctionMatrix`, `FunctionTruncation`, and `NuclearNorm` equal their spectral/operator counterparts. Prove the positive-part identity for symmetric `D`, `‖D‖_* = 2 tr(D₊) − tr D`, pinching contraction in nuclear norm, the min-max compression bound `0 ≤ h_i ≤ a_i`, and the ordered-eigenvalue nuclear perturbation inequality. These are proof obligations, not new hypotheses.

2. **Ridge compression, source Lemma 2.** Define `f_s(x)=x/(s+x)` for `s>0`. For any real PSD `A`, any rank-`k` orthogonal projection `P`, `C=PAP`, `H=C|range(P)`, and every `s,c>0`, prove

   ```text
   tr((f_s(C)−f_s(A))₊)
     ≤ 2/(s+c) · [tr((C−A)₊)+tr((cI_k−H)₊)].
   ```

   The first proof may assume `H` positive definite and use the exact block equations (2)–(7) of the source. Remove that assumption by `A_r=A+rP`, `C_r=C+rP`, `r↓0`; their difference remains `C−A`. Positive-part trace and resolvent continuity must be proved. The lemma includes singular `H`, zero `A`, arbitrary orientation of `P`, and all `s,c>0`.

3. **Matched leading spectrum.** In the `τ=∑_{i≥k} a_i>0` branch put `c=a_(k−1)>0` (the source uses one-based `a_k`), `g=(s+c)⁻¹`, and let `B₀` have the actual top `k` eigenvalues of `A` on the selected projection of `Ahat`. Retain its possibly arbitrary orientation. With `C=PAP`, `L=∑_{i<k}a_i−tr H`, `R=‖B₀−C‖_*`, and `e₀=‖A−B₀‖_*−τ`, prove the exact source chain

   ```text
   0 ≤ L,       R+L ≤ e₀,
   e_C := ‖A−C‖_*−τ ≤ e₀+R,
   e_C = L+2 tr((C−A)₊),
   tr((cI_k−H)₊) ≤ L,
   ‖f_s(A)−f_s(B₀)‖_*−τ_s ≤ 5g e₀,
   τ_s := ∑_{i≥k} a_i/(s+a_i).
   ```

   The scalar identity `|f_s(a)−f_s(b)| = s|a−b|/((s+a)(s+b))` is used with `a≥c`, `b≥0`; the resolvent bound between `B₀` and `C` is on `range(P)`, so `f_s(0)=0` makes the complementary blocks vanish. No commutation of `A`, `Ahat`, `B₀`, and `C` is assumed.

4. **Actual selected approximant and constant 11.** With `B=FunctionTruncation k id eigenvaluesAhat QAhat`, retain the chosen `QAhat`, set `r=∑_{i<k}|a_i−b_i|`, and prove `r+τ≤‖A−B‖_*`, `r≤e(B):=‖A−B‖_*−τ`, and `e₀≤e(B)+r`. The source then gives, for every `s>0`,

   ```text
   ‖f_s(A)−f_s(B)‖_*−τ_s ≤ 11/(s+c) · e(B),
   τ_s ≥ τ/(s+c).
   ```

   The constant comes from `5(e(B)+r)+r≤11e(B)`; it is not rounded or asymptotic. If the frozen premise gives `‖A−B‖_*≤(1+ε)τ`, then `e(B)≤ετ`, hence `‖f_s(A)−f_s(B)‖_*≤(1+11ε)τ_s` for every `s>0`. The nuclear eigenvalue perturbation inequality must include repeated eigenvalues and the `n−k` zero eigenvalues of `B`.

5. **General operator-monotone function: mandatory theorem dependency.** The source invokes the Löwner/Chansangiam representation

   ```text
   f(x)=α+βx+∫_{(0,∞)} x/(s+x) dν(s)       (x≥0),
   α=f(0)≥0, β≥0, ν≥0, ∫(1+s)⁻¹ dν(s)<∞.
   ```

   This is a substantial mathematical theorem, **not** a permissible custom axiom, admitted lemma, or premise added to `AdmissibleFunction`. The frozen hypothesis is operator monotonicity for real symmetric PSD matrices of every positive size. Before invoking a standard complex-Hermitian representation theorem, prove its hypothesis by realifying arbitrary complex Hermitian pairs into real symmetric pairs of doubled size and show functional calculus and order commute with realification. Alternatively prove the real-symmetric representation directly. The current pinned Mathlib tree has special-function operator-monotonicity and a power-function integral representation; a read-only search found no general Löwner representation export. This may be the dominant feasibility blocker. If no kernel proof or suitable pinned theorem is available, stop at a *conditional* internal representation gate and do not claim `TransferBound 11` or `Target`.

   Once proved, justify finite-dimensional spectral integration and nuclear-norm triangle inequality with absolute convergence. The constant atom contributes `α(n−k)` to both the selected error and the optimal tail even when `α>0`; the linear atom contributes `β‖A−B‖_*` and `βτ`; each ridge atom uses Gate 4. The exact tail identity is

   ```text
   τ_f = ∑_{i≥k} f(a_i)
       = α(n−k)+βτ+∫ τ_s dν(s).
   ```

6. **Zero-tail and final composition.** If `τ=0`, the frozen premise and `ε≥0` force `‖A−B‖_*=0`, hence `A=B`, including zero matrices. Because `B` is supported on the **selected** projection `P`, `range(A)⊆range(P)`, and `f(A)−f(B)_P=f(0)(I−P)`. Its nuclear norm and the best rank-`k` tail of `f(A)` are both `(n−k)f(0)`. This handles rank deficiency and `f(0)>0` without division by `τ`. For `τ>0`, Gates 4–5 yield the frozen implication. Combine the two branches for every `ε≥0`, including `ε=0`, then witness `C=11` and `1≤11`.

## Boundary and numerical audit

- `k=1`, `k=n−1`, `n=2`: all sums and selected projections must work. The frozen target does not include `k=0` or `k=n`; internal lemmas may, but cannot silently rely on them as additional public hypotheses.
- Ordered eigenvalues may tie at the cutoff; all supplied orthonormal eigenbases and their actual selected `k`-plane are quantified. The proof must not substitute a favorable eigenbasis or require a spectral gap.
- `A`, `Ahat`, selected `B`, and `H` may be singular. The ridge compression regularization and zero-tail branch are mandatory.
- `f(0)>0` means frozen `FunctionTruncation k f` is **not** the ordinary full functional calculus of the rank-`k` matrix `B`; it is the supported functional calculus `f(B)_P`. This distinction is required in the integral gate.
- The frozen nuclear norm and all inequalities are exact real statements. No floating-point check, finite numerical sample, asymptotic notation, or probabilistic premise proves a gate.

## Verification discipline

Implement only after independent mathematical review of this frozen contract. Start with narrow, unimported modules and source-locked exact signatures. Direct pinned Lean/LeanCert kernel checks and independent source/signature audits precede aggregate imports. A conditional result may state its missing representation or finite-matrix lemma as a hypothesis **only** if named and reported as partial; the public frozen `Target` must never be proved from such a hypothesis. The first sensible coding stage is Gate 1 or the standalone ridge compression lemma, not the final theorem.
