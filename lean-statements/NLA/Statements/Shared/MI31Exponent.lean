import Mathlib.Data.Real.Basic

/-! The finite-or-infinite exponent used by both the live and frozen MI-31
statement boundaries. Keeping the type here makes their targets comparable
in the kernel. -/
set_option autoImplicit false

namespace NLA.Statements.MI31

inductive ExtendedExponent where
  | finite (q : ℝ)
  | infinity

end NLA.Statements.MI31
