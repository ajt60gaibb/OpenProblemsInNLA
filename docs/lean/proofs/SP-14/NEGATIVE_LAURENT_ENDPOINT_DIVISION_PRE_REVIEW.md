# SP-14: finite negative Laurent endpoint division

**Author:** `/root/sp14_base_proof`, 10 October 2026. **Status:** frozen mathematical/numerical pre-implementation contract. Frozen Target: `lean-statements/NLA/Statements/SP14.lean`, SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. Canonical source: `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex`, SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`, especially the endpoint cancellation argument at lines 765–785. Approved parent contract: `ENDPOINT_WIENER_CANCELLATION_PRE_REVIEW.md` SHA-256 `6bd5adcd58819b4ad585bb25fd565ee33453c51c341e58e1ccf136a6cbfe9175`. Audited source prerequisite: `FiniteLaurentBackground.lean` SHA-256 `21ddde26cfbbfec236f7c9ddc3b212702baa56c0ceef333e9289f09f5a052e7b`; use its exact `negativeLaurent` definition, with real coefficients and strict frequencies `−1,…,−u`. The later `RegularizedBaseFactorFourier.lean` and `RegularizedFactorWiener.lean` are separate gates and are not assumptions for this finite identity.

## Exact public Lean surface

```lean
theorem negativeLaurent_endpoint_factor (u : ℕ) (p : Fin u → ℝ)
    (hcontact : negativeLaurent u p (-1 : Circle) = 0) :
    ∃ q : Fin u → ℝ,
      (∀ j : Fin u, j.val = 0 → q j = 0) ∧
      (∀ s : Circle,
        negativeLaurent u p s =
          (1 + (s : ℂ)) * negativeLaurent u q s)
```

The `q` vector has the **same finite index set** as `p`; its first coefficient is zero, so `negativeLaurent u q` has no `s^{-1}` term and all its frequencies are at most `−2`. The equality holds for every `s : Circle`, not merely at the contact point. The theorem asserts existence from the actual endpoint equation rather than assuming the factorization as a surrogate hypothesis. No continuity premise is needed for these finite Laurent sums.

## Finite algebra and endpoints

Write `p_j=p ⟨j−1,…⟩` and `q_j=q ⟨j−1,…⟩` for one-based `1≤j≤u`. Set `q_1=0`. Equating the coefficient of `s^{-j}` in `(1+s)Q` gives

- `p_j=q_j+q_{j+1}` for `1≤j≤u`, with the convention `q_{u+1}=0`;
- thus `q_{j+1}=p_j−q_j` recursively for `1≤j<u`;
- and the last consistency equation `p_u=q_u` is equivalent to `P(-1)=∑_{j=1}^u(-1)^j p_j=0`.

To check the sign, the recursive value is `q_j=∑_{i=1}^{j−1}(-1)^{j−1−i}p_i` for `j≥2`; for `u=2`, `q_2=p_1` and endpoint cancellation requires `p_2=p_1`. Multiplying `q_j s^{-j}` by `s` moves it to `s^{-(j−1)}` because `s≠0` on `Circle`.

The empty case `u=0` has unique empty `p,q` and `0=(1+s)0`. At `u=1`, the endpoint equation is `−p_1=0`, so `p_1=0` and `q_1=0`. The nonempty exact test is `u=2`, `p=(t,t)` for any real `t`, `q=(0,t)`: `t(s^{-1}+s^{-2})=(1+s)t s^{-2}`. The test includes `t=0`, and at `s=-1` both sides are zero.

This gate supplies only finite endpoint division. It does not establish Fourier coefficients of `g₀P₋`, weighted convolution, simultaneous five smallness bounds, any background inverse, the conformal map, or the frozen negative Target. Implement only after independent mathematical review of this exact signature, in a new unimported source with a separate final source/signature/imported-kernel audit.
