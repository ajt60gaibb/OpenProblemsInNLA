# Elimination over a block of stages: exact contract

Proposed by root before implementation. Use the existing padded left operators
`eliminationRows A path t` and the literal original row coordinates.

Define J(A,path,t,0)=I and recursively apply `eliminationStep` at absolute
stage t+s to J(A,path,t,s), with the actual trajectory at that stage and its
prescribed pivot. After the ambient dimension the next J is zero, matching
the existing totalization. No restarted trajectory or fresh pivot rule is used.

Prove the following exact deterministic statements:

1. For every A,path,t,s, including invalid paths, actual matrix multiplication
   gives J(A,path,t,s) E(A,path,t)=E(A,path,t+s).
2. If path is admissible, each row of J has l1 norm at most 2^s. The
   exponent counts only this block's stages; no factor 2^t is introduced.
3. If path is admissible, E(A,path,k) A has zero in every column j<k,
   including rows already eliminated. This discharges pivot nonzero at each
   new column; it is not asserted for arbitrary totalized invalid paths.
4. Consequently, for t+s<=n and Gstar the original columns t,...,t+s-1,
   J(A,path,t,s) E(A,path,t) Gstar=0, as an equality of n by s matrices.

Empty blocks and t+s=n retain their literal meanings. These are identities
for the existing GEPP semantics and do not claim a probabilistic estimate.
Independent mathematical review is required before implementation.

Preimplementation independent review by /root/source_statement_author:
Approved all four statements. Linearity in the second matrix argument gives
the composition identity even for invalid paths. Admissibility supplies the
unit multiplier bound and nonzero pivots for the norm and annihilation
claims. Empty and terminal blocks remain valid.
