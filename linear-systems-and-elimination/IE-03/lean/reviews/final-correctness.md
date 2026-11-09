# IE-03 independent final proof correctness review

**APPROVE** the proof at commit `89987eb5059ce5a497c18ce50c9b86f8cf394b86`.
Reviewed on 9 November 2026 by Codex agent `/root/ie03_statement_b`, an
independent AI referee with no implementation role. This is the final
proof correctness and quality review. I previously reviewed the frozen
statement in the separate statement phase.

The reviewed commit identifies the complete set of proof modules, generated
checkpoints and checks, scripts, toolchain pins, and both public interfaces.
I confirmed that the proof sources in the checkout matched this commit and
that the frozen definitions, challenge, and specification still matched
`verification/STATEMENT-SHA256SUMS`.

## Algebraic chain

- In `Path.lean`, `Agree.schur` uses the active index bounds of the pivot and
  of both applications of `skip`. The Schur update therefore depends only on
  the agreed active entries. `PivotPrefix.transport` carries forward the
  corresponding exact terminal prefix, and `Trace.append` transports the
  second prefix to the first prefix's actual endpoint before concatenating
  them. Prefix growth is composed by the maximum. `Trace.complete` requires
  terminal order zero and returns the original `CompletePath` predicate.
- In `Lift.lean`, `double` partitions each row and column into consecutive
  even and odd copies. The four `double_embed` cases have signs of the
  order-two Sylvester factor. `skip_twice` proves that deleting the same
  current index twice removes the original pair and preserves the order
  and parity of surviving indices. Both choices have valid row and column
  indices, including the last pair in the active square. After the first
  pivot of value $`p`$, the second choice has value $`-2p`$.
  `second_double_pivot` bounds every first Schur entry by
  $`|p|+|p|^2/|p|=2|p|`$, using absolute values and positivity of
  $`|p|`$ for the division. `schur_double_twice` proves the four parity
  cases of the exact scalar Schur complement identity. For example, the
  odd–odd block first contains the negative original entry minus the first
  pivot correction. The second correction has the opposite sign and twice
  that magnitude, yielding the negative of the original scalar Schur
  complement. The other three parity cases give the positive scalar Schur
  complement. `PivotPrefix.double` applies this identity inductively and
  doubles the exact peak, including the empty prefix case.
- In `Walsh.lean`, `sum_pairs` partitions the entire Gram sum into even and
  odd columns. In equal-parity rows the contributions add to twice the
  previous row product. In unequal-parity rows they cancel. The active
  index bounds descend under division by two. With the sign condition and
  order-one seed, `walsh_hadamard 12` proves the real sign and Gram
  conditions of the entire order-4096 witness.

## Certificates and final assembly

- `Certificate/Checkpoint.lean` decodes each row from a natural-number word
  into signed integer numerators. Arithmetic after decoding is on unbounded
  integers. The represented matrix is the total function
  `Checkpoint.entries` with its common denominator. The soundness theorem
  checks the entries defined by this function. I independently checked that
  the concrete tables have exactly the expected number of packed rows and
  that their words fit the expected number of slots.
- In `Certificate/Sound.lean`, `square_sound` covers every pair of indices
  below the specified active order. `stepOK` verifies both pivot indices,
  both positive denominators, nonzero pivot numerator, and the whole-square
  weak magnitude bound. The bound transfers through the positive common
  denominator. For current numerators `x, y, z, p`, current denominator
  `d`, next numerator `v`, and next denominator `e`, the check verifies
  `(x * p - y * z) * e = v * (d * p)`. The actual real update is
  `x/d - (y/d)*(z/d)/(p/d) = (x*p-y*z)/(d*p)`. The nonzero facts justify
  clearing denominators even when the pivot is negative. The proof transports
  the exact integer equality into the reals. `trace_sound` follows the
  checked list with those actual updates, rejects a pivot at order zero, and
  casts the rational maximum to the real maximum of the same pivots.
- I decoded the committed hexadecimal row words using integer division and
  remainder in a separate Python check. I compared the declarations and step
  lists to the pivot choices extracted from Andia's pinned source, and
  recomputed the whole-square maxima and every Schur transition with exact
  fractions. The 129 checkpoints match all 124 local choices. I independently
  compared the initial square to the Walsh sign formula and the four bridge
  squares to the corresponding fourfold Kronecker products. The phase
  maxima were 4, 16, 64, 256, and 4608, with active orders 16 to 6, 24 to 8,
  32 to 10, 40 to 12, and 48 to 0 respectively.
- The generated phase modules prove each concrete `stepOK` and phase maximum
  with `decide +kernel`. Each phase derives its `Trace` through
  `trace_sound`. In `Proof.lean`, `seed_checked` binds the first phase to
  `walsh 4`, and `lift_sound` uses exact cross multiplication across every
  entry of each bridge square. The four calls to `next_phase` combine
  the two consecutive doublings with the appropriate next local phase.
  The final trace starts at `walsh 12`, reaches order zero, and has peak
  4608. The two exports use that trace and the full Hadamard proof. The
  universal equality would give 4608 = 4096, which `norm_num` refutes.

The proof uses the order-two algebraic lift to avoid a dense check over all
4096 pivots. The packed tables provide finite input data and the exact
integer checker establishes their claims in Lean. The Python generator is
a reproducibility check for the inputs and theorem source.

## Mechanical evidence and limitations

I independently ran `python3 generate_checkpoints.py --check`. I also
ran an incremental `lake build Solution` and `lake env lean Audit.lean`
on arm64 macOS with Lean 4.33.1. The Solution build completed successfully.
The audit reports exactly `propext`, `Classical.choice`, and `Quot.sound`
for each public declaration. I inspected `verification/local-build-and-axioms.log`
and the solution import chain, including the separation of
`Challenge.lean` from the proof. A scan of the project's Solution sources
found no proof placeholders, native decision calls, or custom axiom
declarations.

I found no blocking proof correctness or quality issue. The exports cover
the order and exact growth of the full counterexample and the universal
negation. The source's first overshoot index and larger-order corollary
remain outside the exports. This review uses the local build and source
evidence. Isolated Linux and Comparator have separate verification gates.
