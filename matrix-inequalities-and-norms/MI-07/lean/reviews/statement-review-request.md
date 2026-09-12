# MI-07 independent statement review request

Status: **statement-only, awaiting two independent approvals**. No Proof.lean or Solution.lean exists. `lake build NLA.MI07.Definitions Challenge` passed (2710 jobs; only seven deliberate Challenge placeholders). The implementer's independent exact Fraction reconstruction passed all displayed rational identities. Source and statement hashes are bound in `statement-freeze.json`.

Please review the complete canonical MI-07 README and Colbrook solution.tex at the pinned base, the actual definitions, all seven Challenge exports, and NUMERICAL_TARGETS. The witness is Colbrook's family at t=5/12, selected so s=sqrt(1+t²)=13/12 is rational and the original constant-one target fails by the trace gap 1/3 for every complex unitary pair. The source's stronger no-finite-C theorem is outside the advertised formal scope.

The actual maximal modulus is limUnder of the exact CFC positive-integer root sequence, enumerated by m=r+1. The generic unique-limit identification and all three witness convergence statements are mandatory proof exports. No convergence assumption is added to the counterexample or full conjecture negation. A generic all-matrix existence theorem is not claimed or needed for this negative answer. The spectralNorm definition explicitly selects the true L2 operator norm, and a separate generic equivalence export connects the sequence's ordinary matrix topology to spectral-norm convergence. The target's comparison is ordinary PSD order, not Olson spectral order or a pointwise matrix order.

Check actual matrix CFC/natural-power instances, adjoint orientation, dimension/field/quantifier fidelity, positive exponent indexing, all three limits, full complex unitaries, and every rational Gram/projection/trace value independently. Record approve/request_changes and exact hashes before proof implementation starts. `elaborated-statements.log` and `inspection-result.json` retain the elaboration inspection.

Frozen mathematical boundary:

- `NLA/MI07/Definitions.lean`: `369e99eaf3df8a8bbfb214973129ab71fbc95445ba9d176e91d52bca3bc46bc5` (3041 bytes).
- `Challenge.lean`: `62fee2804dc12a4ad7edecfa8c1dda2dc39acc2d94475d29805e8e55c3288a59` (3314 bytes).
- `NUMERICAL_TARGETS.md`: `70272f54de929a95347db186b09b66d534313eed87ab7daa8e7fe5c8aaa8bd1e` (11543 bytes).
