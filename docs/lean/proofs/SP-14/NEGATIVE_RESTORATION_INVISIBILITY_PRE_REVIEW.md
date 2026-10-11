# SP-14 negative restoration and earlier-section invisibility: pre-proof contract

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen for independent mathematical and Lean-signature review before implementation. The frozen original statement is `lean-statements/NLA/Statements/SP14.lean` (SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`); the source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex` (SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`), especially the localized-restoration lemma and “Exact selection and the infinite symbol.” Permanent problem identity and the frozen negative `Target` stay unchanged. The reviewed positive-packet component is `PositivePacketInvisibility.lean` (SHA-256 `90df55a41491c60d442df3679d1808c2c77a66d8e66fe8dbffe940151c3c8d1f`).

## Exact finite packets

For `m,q:ℕ`, `v:Fin q→ℂ`, and `s:Circle`, define the finite Laurent polynomial

\[
L_{m,q,v}(s)=\sum_{d=0}^{q-1}v_d s^{d-m}.
\]

For `0≤r≤m`, let

\[
c_{m,r}=(-1)^{m+1+r}\binom mr 2^{-m},\qquad
K_m(s)=\sum_{r=0}^{m}c_{m,r}s^{-m-1-r}.
\]

The source writes the same packet as

\[
K_m(s)=(-s)^{-m-1}\bigl((1-s^{-1})/2\bigr)^m.
\]

The formal proof must establish this identity for every `s:Circle`, including `m=0`. Define `D_{m,q,v}(s)=L_{m,q,v}(s)-L_{m,q,v}(-1)K_m(s)`, and the actual perturbation of the frozen Toeplitz symbol by `z↦zD_{m,q,v}(z²)`. These are finite continuous functions. `v` may be complex; the source's selected vector is real, so this is an algebraic generalization.

Proposed public Lean interface (names may be adjusted, but mathematical types and conclusions must be retained):

```lean
noncomputable def negativeL (m q : ℕ) (v : Fin q → ℂ) (s : Circle) : ℂ :=
  ∑ d : Fin q, v d * (s : ℂ) ^ ((d.val : ℤ) - (m : ℤ))

noncomputable def restoringCoeff (m r : ℕ) : ℂ :=
  (-1 : ℂ) ^ (m + 1 + r) * (Nat.choose m r : ℂ) / (2 : ℂ) ^ m

noncomputable def restoringK (m : ℕ) (s : Circle) : ℂ :=
  ∑ r ∈ Finset.range (m + 1), restoringCoeff m r *
    (s : ℂ) ^ (-((m + 1 + r : ℕ) : ℤ))

noncomputable def restoredD (m q : ℕ) (v : Fin q → ℂ) (s : Circle) : ℂ :=
  negativeL m q v s - negativeL m q v (-1) * restoringK m s

noncomputable def restoredNegativePacket (m q : ℕ) (v : Fin q → ℂ)
    (z : Circle) : ℂ :=
  (z : ℂ) * restoredD m q v (z ^ 2)

theorem restoringK_source_formula (m : ℕ) (s : Circle) :
  restoringK m s =
    (-(s : ℂ)) ^ (-((m + 1 : ℕ) : ℤ)) *
      ((1 - (s : ℂ) ^ (-1 : ℤ)) / 2) ^ m

theorem restoringK_at_neg_one (m : ℕ) : restoringK m (-1) = 1

theorem restoredD_at_neg_one (m q : ℕ) (v : Fin q → ℂ) :
  restoredD m q v (-1) = 0

theorem toeplitz_add_restoration_invisible (a : Circle → ℂ)
    (ha : Continuous a) (λ : ℂ) (m n : ℕ) (hn : n ≤ 2 * m + 1) :
  Toeplitz (fun z => a z + λ * (z : ℂ) * restoringK m (z ^ 2)) n =
    Toeplitz a n

theorem toeplitz_add_restoredNegativePacket_invisible
    (a : Circle → ℂ) (ha : Continuous a)
    (m q p n : ℕ) (v : Fin q → ℂ)
    (hm : 8 * p ≤ m) (hq : 2 * q ≤ m) (hn : n ≤ 2 * p + 1) :
  Toeplitz (fun z => a z + restoredNegativePacket m q v z) n =
    Toeplitz a n
```

The first invisibility theorem concerns **only** the restoring `K_m` term at its own order. The full `D` theorem concerns **earlier** sections of order at most `2p+1`, with a later-stage separation `m≥8p` and support bound `2q≤m`. In the source's exact stage choice, `m` is divisible by eight and `q=3m/8`, so `2q=3m/4≤m`; the next selected `m` is at least eight times the previous `p`. The proof may package the sufficient inequalities differently, but must retain a checked specialization to these source parameters. It must never claim that full `D` is invisible to `T_{2m+1}`: `L` is selected precisely to change that section.

## Exact checks and proof route

The binomial theorem gives the finite expression for `K_m`. At `s=-1`, every coefficient-times-mode term equals `2^{-m}\binom mr`; their sum is one. Thus `D(-1)=L(-1)-L(-1)·1=0`. The endpoint is valid for `m=0`: `K_0(s)=-s^{-1}`, so `K_0(-1)=1`.

Under `z↦zK_m(z²)`, term `r` has integer circle frequency

\[
1-2(m+1+r)=-2m-1-2r.
\]

For `n≤2m+1`, every row-minus-column index of `Fin n` lies in `[-2m,2m]`, hence the restoring term's Fourier coefficient vanishes there by the reviewed `FourierCoefficient_circle_mode`. This includes `m=0,n=0/1`. The frozen real interval integral is additive with a continuous background; the proof must establish the packet's continuity before using integral linearity.

Under `z↦zL_{m,q,v}(z²)`, term `d<q` has frequency

\[
1+2(d-m).
\]

The restoring term has frequencies `-2m-1-2r`. If `8p≤m`, `2q≤m`, and `d<q`, then both sets are strictly below `-2p`, outside every row-minus-column diagonal for `n≤2p+1`. Hence the **full** restored perturbation is invisible to that earlier section. If `q=0`, the raw sum and `L(-1)` are zero, so the conclusion also covers the empty endpoint without an artificial positive-q assumption. With `p=m=0`, `q=0` necessarily, and the full packet is zero.

## Scope and unproved obligations

These theorems are exact finite packet algebra and finite Toeplitz persistence. They do not supply the selected vector `v`, its jet equations, multiplicity at `±1`, norm budgets, regularity, or the infinite limit. In particular the source's present-stage `L_v` is **visible** to `T_{2m+1}`. Final `Target` still requires a continuous symbol with no inner or outer annular extension, eigenvalue factors of positive asymptotic multiplicity along a selected subsequence, an isolated compact-support test, and a canonical-versus-empirical gap. The base exterior symbol has an outer extension and is not itself the counterexample.
