# MI27 frozen C15, C19 and C20 final assembly

Author: Codex agent /root/nr04_mf14_final_referee_a, contributing for
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology. Analytic resolution: Sidney Holden,
Flatiron Institute, Simons Foundation. Prior MI24/MI27 sources retain credit.

These exact statements are copied from the unchanged frozen Challenge,
whose original two-review gate is retained. Root explicitly assigned their
implementation after actual local C11 success in recovery-114. No new
mathematical helper header or premise is introduced by this plan.

C15 uses one C10 cutoff for every unitary flow value, C12's actual weighted
entropy identity at t and 0, C09 finite hockey-stick differences, positive
kernels and C14's mass bound. It does not differentiate a hockey-stick
integral. C12 is an ordinary imported proved theorem in
NLA.MI27.WeightedEntropy; no placeholder axiom or provisional hypothesis.

C19 applies C03's positive trace normalization, C15 to the normalized
strict density pair, and the already proved C16 derivative at zero. The
ordinary HasDerivAt.le_of_lip' theorem bounds the actual derivative. C14 at
R=1 establishes h(a,b)>=0. C20 uses the existing actual Hermitian sign
witness C18 and exact Gram equality C17, retaining zero commutators.

Root alone compiles serially, one thread, 4096 MiB. This author runs no
Lean or Comparator. These sources do not change any published ID or target.

```lean
theorem entropy_trajectory_lipschitz {n : ℕ} (hn : 1 ≤ n) (ρ σ H : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) (hH : H.IsHermitian)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (t : ℝ) :
    |entropy ((a : ℂ) • ρ + (b : ℂ) • conjFlow H σ t) -
        entropy ((a : ℂ) • ρ + (b : ℂ) • σ)| ≤
      |t| * opNorm H * h a b

theorem logarithmic_commutator_dual_bound {n : ℕ} (hn : 1 ≤ n) (A B H : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (htrace : Matrix.trace (A + B) = 1)
    (hH : H.IsHermitian) :
    let a := trR A
    let b := trR B
    let K := (-Complex.I) • comm B (logM (A + B))
    0 ≤ h a b ∧ |trR (H * K)| ≤ opNorm H * h a b

theorem logarithmic_commutator_bound (n : ℕ) (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (htrace : Matrix.trace (A + B) = 1) :
    traceNorm (B * logM (A + B) - logM (A + B) * B) ≤
      -(trR A) * Real.log (trR A) - (trR B) * Real.log (trR B)
```
