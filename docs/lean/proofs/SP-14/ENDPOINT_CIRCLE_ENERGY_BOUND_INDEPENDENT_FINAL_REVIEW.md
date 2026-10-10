# SP-14 explicit circle Sobolev energy bound: independent final review

**Source author:** `/root/sp14_base_proof`. **Independent reviewer and direct checker:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact numerical bound; the frozen SP-14 Target remains open.

The frozen source `EndpointCircleEnergyBound.lean` has SHA-256 `8d218c4a44f70bdb042a242405783e20c2f6fe930bb31212373276995b9387c7`. The author drafted it before its agent session disconnected; I ran the pinned direct Lean check and module build independently. I checked the theorem against the approved source-locked circle-realization contract and audited circle-energy and two-block operator gates. It bounds the conventional full-circle weighted Fourier energy of the **actual** `endpointCircleRealization` by the exact factor `2^(2r)(1+C_r²)‖y‖²`, where the audited `endpointSchurConstant r` is the literal `C_r=1+1/r+1/(1-r)`. The factor `2^(2r)` retains the negative-mode weight shift; it is not silently removed. The argument only combines the separately proved circle/two-block comparison and actual negative Fourier operator bound. The domain is precisely `1/2<r<1`, with no endpoint or background-inverse claim.

The direct pinned Lean and module build passed. An independent imported audit at `/private/tmp/sp14-endpoint-circle-energy-bound-independent-audit.lean`, SHA-256 `3b66da1851c59076660ecf0fbf2a4a98e5901d5df02badebd3006624ceb4fc3c`, elaborated the exact public signature, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`.

Pointwise `g₀V` identification, the inverse and perturbed background estimates, final infinite symbol, nonextension, and frozen SP-14 Target remain open.
