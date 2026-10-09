# IE-26 implementation correspondence

Author of the implementation and specification: OpenAI Codex AI agent
/root/statement_design, 2026-09-28. Before implementation, both independent
/root and /root/inventory specification approvals were checked against every
bound input, including final specification SHA-256
a8510023e197fa7c7544936a7e036897b9e1eb5b688346dccf07b946cff336b8.
No canonical source, ID, status, metadata or dependency pin was changed.

Width is exactly 2*N+1. Frequency casts j.val and N to real numbers before
subtracting, so every signed frequency -N,...,N is present once. Spacing is
2*pi/Width, and Node is (Frequency+s)*Spacing for every shift. Admissible
uses the full weak coordinate bounds |s_k|<=alpha, with no sampling, sorting,
wrapping or restriction on signs. The complex exponential embeds the entire
real frequency-times-node expression and multiplies it by the genuine
imaginary unit with positive sign.

EvaluationMatrix has node rows and frequency columns and is unnormalized.
FourierMatrix multiplies each entry by the real reciprocal square root of
Width embedded in the complex field. Interpolant deliberately uses
EvaluationMatrix inverse, applied by the actual Matrix.mulVec to the complete
complex data vector, followed by the complete frequency sum. There is no
accidental sqrt(Width) scaling from use of the normalized Fourier inverse.

For each admissible input, neighboring node gaps and the circular last-first
gap are at least Spacing*(1-2*alpha)>0. Consequently the circle nodes are
distinct, and EvaluationMatrix is an invertible diagonal times an ordinary
Vandermonde matrix. FourierMatrix differs by a nonzero scalar. Thus both
imported total matrix inverses are genuine inverses everywhere used by the
target. This mathematical correspondence does not add a determinant promise
or discard any original input. Proving that fact inside Lean is future proof
work, not a prerequisite for stating the concrete proposition.

LebesgueConstant is the real supremum over all complex data vectors whose
every coordinate has modulus at most one and every real x in [-pi,pi]. Its
value is the modulus of the actual Interpolant. The finite complex polydisk
and closed interval form a nonempty compact set, and evaluation is continuous,
so this supremum is a genuine finite attained maximum. Continuity of each
trigonometric polynomial also identifies its interval maximum with the
original L-infinity essential supremum. No unbounded or empty-supremum default,
real-only data restriction, cardinal-function assumption, or discrete grid
maximum replaces the original operator norm.

InverseNorm is exactly the norm of LinearMap.toContinuousLinearMap applied
to Matrix.toEuclideanLin of FourierMatrix inverse. In the pinned Mathlib,
toEuclideanLin is the toLpLin 2 2 equivalence into complex Euclidean spaces
(PiL2.lean), and toContinuousLinearMap retains the same linear action
(FiniteDimension.lean). This is therefore the genuine induced spectral norm,
not a function-space entrywise norm, Frobenius norm or interpolation norm.

FirstBound chooses a positive real constant before every N, alpha and shift.
The full numerator N^(2*alpha)-1, denominator alpha*(1-2*alpha), N>=2 and
0<alpha<1/2 match the original. SecondBound quantifies 1/4<alpha<1/2 first,
then one positive alpha-dependent constant before every N and shift, and uses
N^(4*alpha-1) with no logarithmic loss. Both real powers use Mathlib real
exponentiation, and all subtractions in exponents and denominators are real.
The endpoints and weak non-strict conclusions are retained exactly.

FirstBound and SecondBound are separately exported closed Prop definitions;
Target is their conjunction. All three have explicit #assert_statement,
#assert_trust kernel and axiom reports under leancert.trust="kernel". Their
fresh pinned Lean 4.33.1 macOS builds succeeded with only propext,
Classical.choice and Quot.sound. The frozen copy was created only after the
live build passed. A fresh actual rfl equality theorem was then compiled and
kernel trust checked for each of FirstBound, SecondBound and Target, with the
same standard three axioms. No merely textual equality was substituted.

Author-local build and evidence directories are /private/tmp/nla-ie26-build
and /private/tmp/nla-ie26-evidence. The latter contains results.json,
identity-result.json and live/frozen/CheckIE26 logs. Independent final review
must bind the live and frozen source, local infrastructure closure and pinned
dependencies as well as these correspondence notes. No target proof, sampled
numerical certificate, Linux Comparator pass or resolution credit is claimed
from these successful statement elaboration and identity checks.
