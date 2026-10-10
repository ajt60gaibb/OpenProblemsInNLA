# SP-14 positive packet invisibility: pre-proof contract

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen for independent mathematical and Lean-signature review before implementation. This is a small exact component of the final packet construction in `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex` (SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`), Section “Exact selection and the infinite symbol.” The frozen original statement is `lean-statements/NLA/Statements/SP14.lean` (SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`). Permanent problem identity and target stay unchanged.

## Exact packet and public claims

The source’s positive `g`-variable packet is `Q_m(s)=τs^m(1+s)`. Under its fixed transformation `a(z)=zg(z²)`, the corresponding circle perturbation is exactly

```lean
noncomputable def positivePacket (τ : ℂ) (m : ℕ) (z : Circle) : ℂ :=
  τ * ((z : ℂ) ^ (2 * m + 1) + (z : ℂ) ^ (2 * m + 3))
```

Prove, for every `m,n:ℕ` including zero, arbitrary `τ:ℂ`, and every **continuous** background `a:Circle→ℂ`:

```lean
theorem positivePacket_fourier (τ : ℂ) (m : ℕ) (k : ℤ) :
    NLA.Statements.SP14.FourierCoefficient (positivePacket τ m) k =
      τ * (if (2 * m + 1 : ℕ) = k then 1 else 0) +
      τ * (if (2 * m + 3 : ℕ) = k then 1 else 0)

theorem toeplitz_add_positivePacket_invisible (a : Circle → ℂ)
    (ha : Continuous a) (τ : ℂ) (m n : ℕ) (hn : n ≤ 2 * m + 1) :
    NLA.Statements.SP14.Toeplitz (fun z => a z + positivePacket τ m z) n =
      NLA.Statements.SP14.Toeplitz a n
```

In the first signature, the frequency comparisons are interpreted as integer comparisons after coercion; an implementation may write `((2 * m + 1 : ℕ) : ℤ) = k` and likewise for `2*m+3` to disambiguate Lean parsing. This exact formula implies the coefficient at frequency `2m+1` is `τ`, since the second frequency differs by two. It also implies every packet coefficient at a matrix diagonal frequency `i-j` for `i,j:Fin n` vanishes when `n≤2m+1`.

An optional algebraic lemma may record `Q_m(-1)=0` as

```lean
τ * ((-1 : ℂ) ^ m * (1 + (-1 : ℂ))) = 0.
```

This is the source’s endpoint cancellation that keeps the positive stage packet zero at `s=-1`; it must not be confused with a claim that the circle perturbation vanishes at every point satisfying `z²=-1` without the correct `zQ_m(z²)` algebra.

## Proof and endpoint checks

The exact frozen `FourierCoefficient` is linear in the symbol for the continuous background and the continuous finite packet: both interval integrands are integrable. Apply the independently audited `FourierCoefficient_circle_mode` to the two integer modes `2m+1` and `2m+3`, with the scalar factor `τ`. This proves the displayed Fourier formula for **all** integer `k`, including negative frequencies. For `i,j:Fin n`, the row-minus-column diagonal index `k=(i:ℤ)-(j:ℤ)` satisfies `|k|≤n-1≤2m`, so it cannot equal either positive packet frequency. Therefore the Toeplitz section is unchanged entrywise. At `m=0,n=1`, its only diagonal frequency is zero while the packet modes are one and three, giving a one-by-one unchanged section. At `n=0`, both matrices are empty and the identity is immediate. The explicit `ha` matches the continuity premise in the frozen `OriginalConjecture` and avoids relying on unstated linearity of totalized integrals for arbitrary functions.

## Scope and remaining Target obligations

This is a **packet-specific** finite-section invisibility result, so it contributes to persistence of previously selected characteristic factors when future positive packets are added. It does not prove invisibility of the restoring negative packet `D_v`, stage selection, multiplicity at `±1`, or existence of the final infinite symbol. The final source requires both-sided nonextension (positive and negative coefficient root limsups one), a continuous compactly supported test separated from the symbol range, canonical integral zero, and a positive empirical subsequence gap. The positive-packet coefficient alone does not establish nonextension: the later construction must show its exact coefficient survives all other stage corrections and decays subexponentially. The base exterior symbol retains an outer extension and is not the final counterexample.
