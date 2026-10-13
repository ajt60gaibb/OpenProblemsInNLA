# TR-14 finite moment algebra: exact pre-proof contract

**Author:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Status:** mathematical and proposed Lean contract for independent review **before** implementation. This document certifies no TR-14 Lean proof. The unchanged final target is `NLA.Statements.TR14.Target`, for every `m≥3`, `n≥2`, moment vector, and width `r≥0`.

## Exact representation and zero endpoint

Put `q=n−1`, `D=mq`, and use the frozen zero-based `Hankel h`. For `0≤d≤D`, an apolar coefficient vector `g : Fin(d+1) → ℂ` means exactly

\[
  \sum_{i=0}^{d} g_i h_{i+j}=0\qquad(0\le j\le D-d).
\]

It represents the homogeneous binary form `G(X,Y)=∑_{i=0}^d g_i X^(d−i)Y^i`; trailing zero coefficients remain meaningful because the homogeneous degree is `d`. For `d>D`, the source defines the whole degree-`d` space to be apolar, but the foundation theorem below only quantifies over `d≤D`. The middle catalecticant has **rows** `0≤i≤⌊D/2⌋`, **columns** `0≤j≤⌈D/2⌉`, and entry `h_{i+j}`. No conjugation occurs in the pairing or catalecticant.

First prove `HankelIndex` is surjective onto `Fin(D+1)` for target-range `m,n`: every `j≤mq` is a sum of `m` digits between `0` and `q`. Consequently `Hankel h=0 ↔ h=0`. The existing width-zero lemmas then handle the zero tensor directly; do not assign a quotient algebra or a projective support count to `h=0`. For nonzero `h`, `I₀=0`, so the smallest nonzero apolar degree `r₀` satisfies `1≤r₀`. At `d=⌊D/2⌋+1`, the apolar map has `d+1` columns and `D−d+1` rows, so a nonzero kernel exists and `r₀≤⌊D/2⌋+1`. This includes the boundary `D=2r₀−2` and the `r₀=1` case. Keep `r₀` distinct from the target's arbitrary width `r`.

## Proposed Lean interfaces

The following signatures are **API sketches**, not compiled Lean. Implementations may use `Polynomial`, homogeneous forms, `AdjoinRoot`, or an explicit finite quotient, provided the definitions elaborate to the equations above and the public mathematical assertions remain equivalent.

```lean
def Apolar (h : Fin (D + 1) → ℂ) (d : ℕ) (hd : d ≤ D)
    (g : Fin (d + 1) → ℂ) : Prop :=
  ∀ j : Fin (D - d + 1),
    (∑ i : Fin (d + 1), g i * h ⟨i.val + j.val, by omega⟩) = 0

def Frobenius (A : Type*) [CommRing A] [Algebra ℂ A]
    (λ : A →ₗ[ℂ] ℂ) : Prop :=
  ∀ a : A, (∀ b : A, λ (a * b) = 0) → a = 0

def MiddleCatalecticant (h : Fin (D + 1) → ℂ) :
    Matrix (Fin (D / 2 + 1)) (Fin ((D + 1) / 2 + 1)) ℂ :=
  fun i j => h ⟨i.val + j.val, by omega⟩
```

Here `(D+1)/2=⌈D/2⌉`. The implementation must make the index bound explicit; using `Fin(D+1)` for moments must not silently truncate an out-of-range coefficient. If the actual matrix API transposes the two axes, state and prove that its rank agrees with this matrix.

Proposed public theorem interfaces, with `A_g := ℂ[t]/(g)` and `t̄` its residue class, are:

```lean
moment_index_surjective (hm : 3 ≤ m) (hn : 2 ≤ n) :
  Function.Surjective (HankelIndex (m := m) (n := n))

minimal_apolar_exists (h : Fin (D + 1) → ℂ) (hh : h ≠ 0) :
  ∃ r₀, 1 ≤ r₀ ∧ r₀ ≤ D / 2 + 1 ∧
    (∃ g ≠ 0, Apolar h r₀ ... g) ∧
    (∀ d < r₀, ∀ b, Apolar h d ... b → b = 0)

moment_quotient_frobenius (hh : h ≠ 0)
    (g : ℂ[X]) (hg_monic : g.Monic)
    (hg_degree : g.natDegree = r₀)
    (hg_apolar : Apolar h r₀ ... (coefficients g))
    (hminimal : no nonzero apolar vector in any degree d < r₀) :
  ∃ λ : A_g →ₗ[ℂ] ℂ,
    (∀ j : Fin (D + 1), λ (t̄ ^ j.val) = h j) ∧
    Frobenius A_g λ ∧ Module.finrank ℂ A_g = r₀

middle_rank_eq_minimal_apolar (hh : h ≠ 0) :
  Matrix.rank (MiddleCatalecticant h) = r₀
```

The displayed binder ellipses denote the dependent bound proofs and `r₀`/`D` parameters fixed in the eventual declaration, **not** extra mathematical assumptions. In particular, `middle_rank_eq_minimal_apolar` is about the original moment vector, not only a changed-coordinate vector. It must not acquire a genericity, squarefree, invertibility of the catalecticant, or selected-width premise.

## Quotient and rank proof obligations

A minimal homogeneous apolar form may have a root at infinity. The source first applies an invertible `GL₂(ℂ)` coordinate change to move its finitely many projective roots away from infinity, then scales so `g(t)=G(1,t)` is monic of **degree exactly** `r₀`. The formal development must either prove this normalization and invariance of the apolar spaces, middle rank, and the induced invertible action on each `n`-dimensional tensor mode, or give a coordinate-free quotient proof. A hypothesis that the originally selected apolar form already has a nonzero top coefficient cannot replace this step in the public all-`h` theorem.

For monic `g(t)=t^r₀+∑_{i<r₀}g_i t^i`, apolarity is precisely

\[
 h_{j+r₀}+\sum_{i<r₀}g_i h_{j+i}=0
 \quad(0\le j\le D-r₀).
\]

Define `λ` on the quotient basis `1,t̄,…,t̄^(r₀−1)` by the first `r₀` moments. Induction on `j`, using that recurrence and **only** its stated range, must give `λ(t̄^j)=h_j` for every `0≤j≤D`. This proves the exact multilinear identity `H(p₁,…,p_m)=λ([p₁]⋯[p_m])` for mode polynomials of degree at most `q`; it is not merely equality of low-order moments.

The radical `J={a∈A_g : ∀b, λ(ab)=0}` is an ideal. If nonzero, its quotient is `ℂ[t]/(g')` for a monic proper divisor `g'|g` of degree `<r₀`. Since `λ` descends and agrees with **all** moments through `D`, `g'` supplies a nonzero apolar form of smaller homogeneous degree: its recurrence holds for `0≤j≤D−deg g'`. This contradicts minimality. The case `deg g'=0` would force all moments to vanish and is excluded by `hh`. Thus `J=0` and the bilinear pairing `(a,b)↦λ(ab)` is nondegenerate. Proving only that `λ` is nonzero is insufficient.

Both polynomial spaces of degrees `≤⌊D/2⌋` and `≤⌈D/2⌉` surject onto `A_g`, because both bounds are at least `r₀−1`. The middle matrix is the pullback of the Frobenius pairing through these **two** surjections, so its rank is exactly `dim A_g=r₀`. The proof must cover rectangular `D` odd and square `D` even, including full middle rank in the balanced case.

## Balanced apolar space and local algebra gates

The source's choice lemma has two exact branches. If `D≥2r₀−1`, the degree-`r₀` apolar space is one-dimensional, generated by `G`; polynomial degrees `≤D−r₀` already surject onto `A_g`. If `D=2r₀−2`, that apolar space has dimension **two**: the domain has dimension `r₀+1`, while the relevant moment equations have rank `r₀−1`. No branch `D=2r₀−3` occurs by the degree bound. These are finite-dimensional vector-space dimensions, including `r₀=1` where the nonbalanced degree-`1` apolar space is unique for `D≥1`; the target has `D≥3`. The balanced formula for the final rank must later be proved independent of which nonzero minimal apolar form is chosen; that independence is **not** part of the moment algebra lemma itself.

For later §§3–5, factor the normalized `g=∏_{a=1}^s(t−α_a)^ℓ_a` with distinct `α_a`, positive `ℓ_a`, and `∑ℓ_a=r₀`. The Chinese remainder isomorphism must preserve `t̄`, multiplication, and `λ`; each local restriction `λ_a` is Frobenius. For every nonempty set `J` of factors, with `r_J=∑_{a∈J}ℓ_a`, prove the exact image dimension `dim im(ℂ[t]_{≤q}→A_J)=min(n,r_J)`. Finally prove products of `m−1` degree-`≤q` polynomials span all of `A_g`, since `(m−1)q≥r₀−1`. The empty-product convention is `ℂ·1`. These gates must be available to the arbitrary ordinary-decomposition lower bound, not assumed as new premises of the final Target.

## Source locks and review gate

| Source | SHA-256 |
| --- | --- |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Proof `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Exact full-proof pre-review | `abd73514c57e2d8c5f6a2709273a43ad282c854c8647e99855492f23052a6698` |

Independent mathematical review of this contract is required before Lean implementation. Later compiled lemmas require separate source-hash, exact-signature, LeanCert kernel, and transitive-axiom audits. Partial quotient and catalecticant lemmas must never be reported as the full TR-14 Target.
