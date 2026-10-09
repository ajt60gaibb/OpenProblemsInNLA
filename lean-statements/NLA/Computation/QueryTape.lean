import NLA.Computation.FiniteMachine

/-! Concrete extraction of the finite binary oracle query from the tape head.
Trailing blanks are ignored; a blank before a later bit is malformed. This is
part of the query interface, not an ordinary unit-cost string instruction. -/
set_option autoImplicit false

namespace NLA.Computation.QueryTape

def decodeSymbols : List Symbol → Option Word
  | [] => some []
  | some bit :: rest => (decodeSymbols rest).map (bit :: ·)
  | none :: rest => if rest.all Option.isNone then some [] else none

theorem decodeSymbols_blanks (n : ℕ) :
    decodeSymbols (List.replicate n (none : Symbol)) = some [] := by
  cases n with
  | zero => rfl
  | succ n => simp [decodeSymbols, List.replicate_succ]

/-- Appending blank cells cannot change the decoded finite query. -/
theorem decodeSymbols_append_blanks (xs : List Symbol) (n : ℕ) :
    decodeSymbols (xs ++ List.replicate n none) = decodeSymbols xs := by
  induction xs with
  | nil => exact decodeSymbols_blanks n
  | cons symbol xs ih =>
      cases symbol with
      | none => simp [decodeSymbols]
      | some bit => simp [decodeSymbols, ih]

/-- A well-defined function on the actual quotient tape representation. -/
def readSuffix (suffix : Turing.ListBlank Symbol) : Option Word :=
  suffix.liftOn decodeSymbols (by
    intro a b h
    rcases h with ⟨n, rfl⟩
    exact (decodeSymbols_append_blanks a n).symm)

def read (tape : Turing.Tape Symbol) : Option Word :=
  readSuffix tape.right₀

theorem decodeSymbols_bits (w : Word) : decodeSymbols (w.map some) = some w := by
  induction w with
  | nil => rfl
  | cons bit rest ih => simp [decodeSymbols, ih]

theorem readSuffix_bits (w : Word) :
    readSuffix (Turing.ListBlank.mk (w.map some)) = some w :=
  decodeSymbols_bits w

theorem read_input (w : Word) :
    read (Turing.Tape.mk₁ (w.map some)) = some w := by
  simp only [read, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_right₀]
  exact readSuffix_bits w

end NLA.Computation.QueryTape
