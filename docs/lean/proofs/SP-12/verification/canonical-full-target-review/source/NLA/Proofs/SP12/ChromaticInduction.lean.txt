import NLA.Proofs.SP12.Critical
import NLA.Proofs.SP12.GramSAP
import NLA.Proofs.SP11.GreedyRelabel

/-!
# The discrete chromatic/nullity induction

Two constructive inputs remain explicit: the PSD/SAP strong-delta realization
and an actual one-vertex Gram extension. Deleting a low-degree vertex preserves
chi; extending its induction witness raises ambient dimension and order by one.
The final SP-12 assembly must supply both inputs by proved theorems.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP12

open NLA.Statements.SP12
open NLA.Proofs.SP11

/-- Constructive strong-delta and one-vertex extension suffice for the exact
chromatic bound on the ambient dimension of an actual SAP Gram realization. -/
theorem exists_chromatic_gram_of_strongDelta_and_extension
    (hdelta : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ∃ (d : ℕ) (R : Matrix (Fin n) (Fin d) ℝ),
        d + NLA.Statements.SP11.MinimumDegree G ≤ n ∧
        HasPattern G (gram R) ∧ StrongArnold (gram R))
    (hext : ∀ (h d : ℕ) (G : SimpleGraph (Fin (h + 1)))
      (R : Matrix (Fin h) (Fin d) ℝ),
      HasPattern (G.comap Fin.succ) (gram R) → StrongArnold (gram R) →
      ∃ S : Matrix (Fin (h + 1)) (Fin (d + 1)) ℝ,
        HasPattern G (gram S) ∧ StrongArnold (gram S)) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ∃ (d : ℕ) (R : Matrix (Fin n) (Fin d) ℝ),
        d + (ChromaticNumber G - 1) ≤ n ∧
        HasPattern G (gram R) ∧ StrongArnold (gram R) := by
  intro n
  induction n with
  | zero =>
    intro G
    obtain ⟨d, R, hd, hp, hs⟩ := hdelta 0 G
    refine ⟨d, R, ?_, hp, hs⟩
    rw [chromatic_empty]
    omega
  | succ h ih =>
    intro G
    by_cases hb : ChromaticNumber G - 1 ≤ NLA.Statements.SP11.MinimumDegree G
    · obtain ⟨d, R, hd, hp, hs⟩ := hdelta (h + 1) G
      exact ⟨d, R, by omega, hp, hs⟩
    · obtain ⟨v, hv⟩ := exists_chromatic_preserving_deletion G (lt_of_not_ge hb)
      obtain ⟨d, R, hd, hp, hs⟩ := ih (deleteVertex G v)
      let e := swapZero v
      obtain ⟨S, hP, hS⟩ := hext h d (G.comap e) R hp hs
      let Sback : Matrix (Fin (h + 1)) (Fin (d + 1)) ℝ := fun i => S (e.symm i)
      refine ⟨d + 1, Sback, ?_, ?_, ?_⟩
      · rw [hv] at hd
        omega
      · change NLA.Statements.SP11.HasPattern G ((gram S).submatrix e.symm e.symm)
        exact hasPattern_of_comap G e (gram S) hP
      · exact strongArnold_gram_relabel S e.symm hS

/-- This reduction asserts the whole frozen Target only after both genuine
construction theorems are supplied; neither input is an axiom or hidden field. -/
theorem target_of_strongDelta_and_extension
    (hdelta : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ∃ (d : ℕ) (R : Matrix (Fin n) (Fin d) ℝ),
        d + NLA.Statements.SP11.MinimumDegree G ≤ n ∧
        HasPattern G (gram R) ∧ StrongArnold (gram R))
    (hext : ∀ (h d : ℕ) (G : SimpleGraph (Fin (h + 1)))
      (R : Matrix (Fin h) (Fin d) ℝ),
      HasPattern (G.comap Fin.succ) (gram R) → StrongArnold (gram R) →
      ∃ S : Matrix (Fin (h + 1)) (Fin (d + 1)) ℝ,
        HasPattern G (gram S) ∧ StrongArnold (gram S)) : Target := by
  intro n _hn G
  obtain ⟨d, R, hd, hp, hs⟩ :=
    exists_chromatic_gram_of_strongDelta_and_extension hdelta hext n G
  refine ⟨gram R, hp, gram_nonnegativeQuadraticForm R, hs, ?_⟩
  have hr := gram_rank_le R
  omega

#assert_trust kernel exists_chromatic_gram_of_strongDelta_and_extension
#assert_trust kernel target_of_strongDelta_and_extension
#print axioms target_of_strongDelta_and_extension

end NLA.Proofs.SP12
