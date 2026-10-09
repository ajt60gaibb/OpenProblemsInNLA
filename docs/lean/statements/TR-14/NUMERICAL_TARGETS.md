# TR-14: exact statement specification

Author: OpenAI Codex agent `/root` (AI). Phase: preimplementation specification. No Lean target or proof has been implemented.

Canonical source: `tensor-computations/TR-14/README.md` at `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`, SHA-256 `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86`. [ORIGINAL.md](ORIGINAL.md) preserves the entire source byte for byte, including the complete problem, history and attribution.

## Exact target and conventions

For every natural m>=3 and n>=2 and every complex list h of length m*(n-1)+1, define the order-m tensor H on tuples i:Fin m -> Fin n by H(i)=h(sum_k (i k).val). This zero-based convention is exactly the source's one-based index sum minus m. All exceptional data and the zero tensor are included.

An ordinary width-r decomposition is a family u:Fin r -> Fin m -> Fin n -> complex with H(i)=sum_j product_k u(j,k,i(k)) for every coordinate tuple i. A symmetric width-r decomposition is c:Fin r -> complex and v:Fin r -> Fin n -> complex with H(i)=sum_j c(j)*product_k v(j,i(k)). Both sums are empty and zero at r=0. Complex multiplication is bilinear, with no conjugation, no normalization, and no Vandermonde restriction.

The planned exact equality-of-ranks formulation: for every natural r, H has an ordinary width-r decomposition if and only if H has a symmetric width-r decomposition. Padding by zero terms makes width-r the same as width-at-most-r. The symmetric-to-ordinary direction absorbs c(j) into one factor (m>=3 supplies one); all tensors admit ordinary finite decompositions, and symmetric tensors admit symmetric finite decompositions over complex numbers. Hence equality of the two minimum widths is equivalent to agreement of these predicates at every r. This formulation does not introduce default ranks on empty witness sets. Reviewers must check both directions of this equivalence before accepting it as the original rank target.

Numerical data: m>=3 and n>=2 inclusive; unrestricted natural r including zero; exact complex equality at every coordinate. No genericity or nonzero requirement is added. No quantitative all-spectrum rank formula from the resolution is imposed, since the original question asks only equality. No numerical certificates are needed.

## Planned Lean boundary and review

The declaration `NLA.Statements.TR14.Target : Prop` will define the question. It will not assert a proof. There will be no target axiom, `sorry`, arbitrary supplied invariant, or unimplemented semantic field. Two independent preimplementation specification approvals are required, followed by two independent reviews of the actual Lean definitions and imported meanings, bound by source hashes.

## Computation and scope

The statement itself requires no interval computation. Exact finite algebra suffices; no domain is reduced. Any future numerical proof uses explicit LeanCert kernel trust. The shared kernel smoke test establishes no catalog target. The existing Solved status and mathematical credits remain as in ORIGINAL.md. This draft claims no mathematical proof, human peer review, or Linux Comparator verification.
