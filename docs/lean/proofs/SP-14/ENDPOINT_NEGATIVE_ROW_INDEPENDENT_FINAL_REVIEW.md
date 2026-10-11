# SP-14 actual negative Fourier row bound: independent final review

**Author:** `/root/sp14_base_proof`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this exact partial gate; the infinite operator remains open.

The frozen source `EndpointNegativeRow.lean` has SHA-256 `d515723d95a6e927bfd6c1a4423e5672cd7a5ffb035f632a7a76053e6cd16aa1`. I checked it against the corrected independently approved infinite-operator precontract. For every `0<r<1`, row `t`, and input cutoff `N`, its public theorem gives `∑ k:Fin N, ‖endpointFiniteFourierEntry r t k.val‖² ≤ endpointSchurConstant r²`, retaining the actual frozen Fourier integral through the finite entry and the exact literal `C_r=1+1/r+1/(1-r)`.

The proof tests the all-cutoff finite complex Fourier-matrix bound with the conjugate selected row at output cutoff `t+1`. Its selected output is the nonnegative real sum `S`; the finite theorem gives `S²≤C_r² S`, and the source proves `S≤C_r²`, including `S=0`. An independent imported audit at `/private/tmp/sp14-endpoint-row-independent-audit.lean`, SHA-256 `0d9cc216ea22d856f8c43a5c5aacfb251b3d2334d70c986ccb8648e83f119dcf`, elaborated the exact public signature, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`. No proof escape or new axiom appears in the source.

The theorem is a finite prefix bound. It does not yet construct the infinite row's unconditional complex sum, the continuous linear operator, the two-sided Sobolev estimate, or the frozen SP-14 negative Target.
