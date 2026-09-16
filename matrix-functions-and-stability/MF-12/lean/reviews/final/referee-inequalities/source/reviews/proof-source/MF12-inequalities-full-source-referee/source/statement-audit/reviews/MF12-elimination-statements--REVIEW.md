# Independent MF-12 statement review

Reviewer: `/root/next_elimination`, independently of the MF-12 statement author
`/root/next_matrix_functions`. This reviewer has not implemented MF-12.

**APPROVE the complete mathematical statement boundary.** I found no blocking
target mismatch, false numerical constant, missing all-word or all-length
quantifier, vacuous main premise, or replacement of the true operator norm.
This is source-only approval. The second independent review and actual Linux
elaboration are still required before the statements are frozen and proof
implementation is authorized. No kernel, Comparator, software-certification,
external human review or published-verification claim is made here.

The approval binds these exact bytes:

| File | SHA-256 |
|---|---|
| `NLA/MF12/Definitions.lean` | `8500b04a60bf3d1cc20dc69e9fa73b26ed56b96d090cf58e7151a10e5da94d6a` |
| `Challenge.lean` | `cf05ff7b1d9d36705c6b329b9d1dc74fe31d26cd7c250f27861e1828ac70611e` |
| `NUMERICAL_TARGETS.md` | `070b8e39fd04a5ed6b7b8c82b27a2aa817739f76f0a00fa2e62e63e707ded651` |
| `comparator.json` | `73bc6de0404bccf15792e48b9ff50d61fa6aa47b6678e84bfc22f6a857473743` |

`CHECKS.json` records all ten reviewed package hashes. The source snapshots and
complete manuscript were independently compared with actual `git show` at
upstream `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`; their hashes agree with the
provenance record. I read the complete original canonical problem, manuscript
sections 1–6, definitions, all 28 proposed declarations, numerical boundary,
source correspondence and formalization metadata. `reviewed-source/` preserves
the exact package bytes inspected. No local Lean/Lake process was run.

## Complete target and boundary semantics

The final declaration retains every real exponent `gamma >= 0`, a fixed
positive dimension, a fixed finite nonempty real matrix family, positive fixed
constants, estimates at every positive integer length, and convergence of the
actual maximal-product nth roots to one. The stronger cardinality-two claim
matches the source construction. The family, dimension and constants are
outside the length quantifier. The target does not replace comparability by
subsequence growth, nor require an unjustified normalized-growth limit.

The norm is explicitly that of `Matrix.toEuclideanCLM` for Euclidean real
vectors. `wordNorms` ranges over every actual length-n list from the family;
chronological reversal has the correct multiplication order. The finite-set
supremum has an independent finiteness, nonemptiness, attainment and domination
obligation. The binary-word bridge does not assume distinctness or injectivity.
The entry maximum includes zero only to give the zero-dimensional definition a
total meaning; positive-dimensional attainment and both operator-norm
comparisons are explicit obligations. Tensor coordinates use the real
Kronecker product and the actual finite-product equivalence. None of these
definitions assumes the desired result.

The exact source arrays U, V, A and P, their signs, the two contracting Jordan
blocks and the fixed lambda = 1/4 are retained. Matrix multiplication gives
U V = I and compressed powers `[1-loss, gain; 0,1]`. The `q=0` gain identity
is true because both relevant real exponents are positive; there is no hidden
zero-to-zero-power convention used to exclude zero gaps. All definitions of
tail weights agree with the reversed chronological product: each earlier
off-diagonal contribution is multiplied by the later diagonal factors.

## Numerical and generic obligations checked

The all-gap estimate is valid for empty lists and arbitrary zero gaps. For
positive gaps, rewrite each term as `(q*w)^alpha*(loss*w)^(1-alpha)` and apply
finite Holder; the two sums are bounded by the total gap length and one. The
telescoping statement supplies that latter budget. The arbitrary-word gap
decomposition and the reset factorization cover no reset, one reset, repeated
resets and zero endpoint gaps. Thus the proposed upper bound concerns every
switching word.

The enlarged constant `1728*H^2` is sufficient: the full rectangular expansion
of `A^r V B U A^s` has 144 summands per entry, followed by a factor six from
the actual matrix norm and the sufficient bound `maxEntry(B) <= 2*n^alpha`.
All A powers have entries bounded by `H = (1-mu)^(-1) >= 1`; the word with no
reset also satisfies the proposed constant. This is an explicit change of
constants, with no change to the norm or exponent.

For the lower word, `q = log_4 n`, `k = floor(n/(q+1))` and the exact remainder
produce length n. At n >= 4, `4^q >= 2*(q+1)` and
`k*q*4^(-q) >= q/(2*(q+1)) >= 1/4`. The elementary Bernoulli denominator bound
then gives `1-(1-loss)^k >= 1/5`. The first coordinate after the final A power
is unchanged, while `||V e_2|| <= 2`; hence the proposed lower constant
`(1/4)^alpha/10` is valid. The three smaller positive lengths are covered by
the A-only word, whose norm is at least one. No missing-length case remains.

The natural Jordan bounds include m=0 and n<m. For n>=m>=1 the top-right
binomial entry is at least `(n/m)^m`; for n<m the unit diagonal suffices.
Every entry is at most `n^m`, giving the stated `(m+1)*n^m` norm upper bound.
The pair with zero is distinct, and words containing zero have zero norm.

The coarse tensor comparison follows from multiplicativity of the actual
entry maximum and `entryMax <= norm <= dimension*entryMax`; it does not rely
on an unproved exact spectral-norm tensor formula. Its fixed dimension factors
give exactly the proposed lifted constants. The lifted pair remains distinct
because a diagonal entry of the Jordan factor is one. Finally, the polynomial
squeeze gives the true nth-root limit, including gamma=0, and splitting a
noninteger nonnegative real exponent into its natural floor and fractional
part covers the entire canonical parameter range.

## Independent supplementary checker and review limits

`check.py` uses exact rational arithmetic only. It independently checks U V,
P squared, compressed powers for q=0 through 12 at alpha=1/2, all 781 gap lists
of length at most four with entries 0 through four, logarithm/division and
Bernoulli inequalities at n=4 through 256, the full six-dimensional prescribed
word and its first coordinate at n=4 through 64, and the Jordan lower-entry
inequality at m=1 through 9 and n=1 through 32. Every check passed. These are
diagnostics supporting the independent general argument above; they do not
replace any universal Lean obligation or prove asymptotics by finite testing.

The Comparator configuration lists all 28 actual Challenge names, with no
replaceable definition holes and only `propext`, `Classical.choice` and
`Quot.sound` permitted. Deliberate proof placeholders are isolated in Challenge;
no proof implementation is present or accepted. Pinned-library declarations
and notation must still pass actual Lean elaboration. Later proof review must
inspect actual kernel and Comparator logs and controls at the measured source
commit, not infer correctness from this approval or a green selected workflow.

Within the applicable Tau Ceti scope, fidelity, complete quantifiers, genuine
definitions, explicit proof bridges, numerical economy, tool transparency and
attribution pass this statement review. Original mathematics remains credited
to Matthew J. Colbrook, Cambridge DAMTP. Formalization belongs to George
Stepaniants, Department of Computing and Mathematical Sciences, California
Institute of Technology. No George email is added. The optional rational-entry,
irrational-example and density corollaries lie beyond the retained canonical
question and are explicitly excluded; their omission does not weaken this
problem's target. No official Tau Ceti endorsement is claimed.
