# RA-10 ridge scalar identities and tail comparison

**Status:** exact mathematical and numerical precontract for independent review; no Lean implementation or proof is claimed.

## Source lock and place in the full target

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/CONSTANT_ELEVEN_TRANSFER_PRE_REVIEW.md` | `43ec3208c3177ff931289bc236f9afa32796c25be96fc07127027654f2623a92` |

The reviewed RA-10 solution uses the ridge atom `f_s(x)=x/(s+x)` in exact Equations (12) and (20). These scalar gates are necessary for the matrix comparison and the precise constant `11`, but do not establish matrix resolvent, nuclear-norm perturbation, positive-integral representation, `TransferBound 11`, or `Target`.

## Exact identities and inequalities

For real `s>0`, `c>0`, `a≥c`, and `b≥0`, all denominators below are strictly positive. Prove the exact source equality and bound:

```text
|f_s(a)−f_s(b)| = s |a−b| / ((s+a)(s+b))
                  ≤ |a−b|/(s+c).                       (12)
```

The equality is an algebraic identity using `(s+a)(s+b)>0`. The inequality follows from `(s+a)≥s+c` and `(s+b)≥s`, and retains coefficient `1/(s+c)` exactly, without floating point or a larger safety constant. It includes `a=b`, `b=0`, and `a=c`.

For `0≤x≤c`, prove the exact pointwise tail comparison

```text
x/(s+c) ≤ f_s(x)=x/(s+x).                             (20, pointwise)
```

For every `n : ℕ`, `k : ℕ`, every `a : Fin n → ℝ` with all `aᵢ≥0` and `aᵢ≤c` whenever `k≤i.val`, sum the pointwise comparison over exactly the zero-based tail index set `T={i:Fin n | k≤i.val}`:

```text
∑_{i∈T} f_s(aᵢ) ≥ (∑_{i∈T} aᵢ)/(s+c).                (20, finite tail)
```

The finite theorem permits empty tails and `n=0` internally. The frozen target retains `n≥2`, `1≤k<n`; the source's one-based `i>k` is this exact zero-based `i.val≥k`. In the positive-tail branch of the full proof, `c=a_(k−1)>0` and the tail bound `aᵢ≤c` must later be derived from the frozen `Antitone` hypothesis, not inserted as a new final premise. These scalar facts make no assertion about arbitrary values of an admissible `f` at negative arguments.

## Proposed Lean module and signatures

Use a separate `NLA.Proofs.RA10.RidgeScalar` module, importing the frozen RA-10 statement. The exact proposed declarations are:

```lean
namespace NLA.Proofs.RA10

def ridgeAtom (s x : ℝ) : ℝ := x / (s + x)

theorem ridgeAtom_abs_sub_eq {s c a b : ℝ}
    (hs : 0 < s) (hc : 0 < c) (ha : c ≤ a) (hb : 0 ≤ b) :
    |ridgeAtom s a - ridgeAtom s b| =
      s * |a - b| / ((s + a) * (s + b)) := by
  ...

theorem ridgeAtom_abs_sub_le {s c a b : ℝ}
    (hs : 0 < s) (hc : 0 < c) (ha : c ≤ a) (hb : 0 ≤ b) :
    |ridgeAtom s a - ridgeAtom s b| ≤ |a - b| / (s + c) := by
  ...

theorem ridgeAtom_tail_lower {s c x : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hx0 : 0 ≤ x) (hxc : x ≤ c) :
    x / (s + c) ≤ ridgeAtom s x := by
  ...

theorem ridgeAtom_tail_sum_lower {n k : ℕ}
    (a : Fin n → ℝ) {s c : ℝ}
    (hs : 0 < s) (hc : 0 < c)
    (ha0 : ∀ i : Fin n, 0 ≤ a i)
    (hac : ∀ i : Fin n, k ≤ i.val → a i ≤ c) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), ridgeAtom s (a i)) ≥
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), a i) / (s + c) := by
  ...

end NLA.Proofs.RA10
```

If Lean's binder syntax requires writing each sum as `∑ i ∈ T, ...`, preserve the same literal filtered set and proposition. The public `ridgeAtom` definition remains exactly `x/(s+x)` for imported exact-signature auditing.

## Review and verification

Independent pre-review must verify the algebraic equality, positive denominators, exact coefficient, boundary values, and one-based/zero-based tail mapping before any Lean implementation. Then direct pinned Lean 4.33.1/LeanCert kernel build, freeze source, and independently audit imported exact signatures and axioms before aggregate import. The complete frozen RA-10 target remains open.
