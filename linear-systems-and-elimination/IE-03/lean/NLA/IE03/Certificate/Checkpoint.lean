/-! An exact active square represented by integer numerators over a common
denominator. Each row word stores its numerators in consecutive 16-bit
slots, least significant first. Subtracting 32768 decodes each slot. The
certificate arithmetic operates on unbounded integers after decoding. -/

namespace NLA.IE03.Certificate

structure Checkpoint where
  denominator : Nat
  rows : Array Nat

def Checkpoint.numerator (A : Checkpoint) (i j : Nat) : Int :=
  Int.ofNat (((A.rows[i]?.getD 0) >>> (16 * j)) &&& 65535) - 32768

end NLA.IE03.Certificate
