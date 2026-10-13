import NLA.Proofs.MF03.FiniteColumnCutEndpoints

/-!
Recursively assemble the explicitly reconstructed cut tuples into the
literal `FiniteValidPath`, in descending factor-label order. The first
transition of a length `n+1` path carries label `n`.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- The chain from cut `n` through cuts `n-1,...,0`, before endpoint
transport. The index proof `n≤N` is proof-irrelevant. -/
def finiteColumnCutPathAux {N m j : ℕ} (hj : j ≤ m)
    (D : FiniteColumnSystem N m j) :
    (n : ℕ) → (hn : n ≤ N) →
      FiniteValidPath m n
        (finiteColumnCutRows hj D n hn)
        (finiteColumnCutRows hj D 0 (Nat.zero_le N))
  | 0, _ => ⟨rfl⟩
  | n + 1, hn =>
      ⟨finiteColumnCutRows hj D n (by omega),
        ⟨⟨finiteColumnCutRows_step hj D n hn⟩,
          finiteColumnCutPathAux hj D n (by omega)⟩⟩

/-- Exact finite path chain reconstructed from the original actual label
sets, with source-locked endpoints and factor-label order. -/
def finiteColumnSystemToPath {N m j : ℕ} (hj : j ≤ m)
    (D : FiniteColumnSystem N m j) :
    FiniteValidPath m N (finitePathStart m j hj) (finitePathEnd m) := by
  have h := finiteColumnCutPathAux hj D N le_rfl
  rw [finiteColumnCutRows_top hj D] at h
  rw [finiteColumnCutRows_zero hj D] at h
  exact h

#assert_trust kernel finiteColumnSystemToPath
#print axioms finiteColumnSystemToPath

end NLA.Proofs.MF03
