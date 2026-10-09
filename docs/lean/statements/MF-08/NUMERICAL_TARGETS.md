# MF-08: reviewed target for a Lean statement

Status: pre-implementation specification. The immutable canonical problem is retained byte for byte in `ORIGINAL.md`; the registered path is `matrix-functions-and-stability/MF-08/README.md`. This document specifies the proposition to formalize, not a proof of the hardness theorem.

## Exact decision language

An input is a triple of rational matrices `A : n×n`, `B : n×m`, `C : p×n` with positive natural dimensions `n,m,p`. The language is over finite binary words. Use the repository's concrete self-delimiting binary encodings of natural dimensions and rational entries, in a fixed row-major order: encode `n,m,p`, followed by all `n²` entries of `A`, all `nm` entries of `B`, and all `pn` entries of `C`. Require a complete encoding with no unchecked suffix; words that do not encode such a positive-dimensional triple are outside the language. The encoding must retain each rational exactly, including sign, numerator, and denominator, and may not use real numbers as input or replace bit size by a real-arithmetic operation count.

The answer is yes if and only if there exists an **unrestricted** real matrix `K : m×p` such that every complex eigenvalue of the real closed-loop matrix `A+BKC` has strictly negative real part. Equivalently, for every `λ : ℂ`, if a nonzero complex vector `v` satisfies `(A+BKC)v = λv`, then `λ.re < 0`. There are no entrywise bounds, norm bounds, fixed gain patterns, sign constraints, or prescribed poles. The strict inequality excludes imaginary-axis eigenvalues. Dimensions and matrix multiplication must be actual finite sums. The language is a decision predicate; it need not be shown decidable or in NP.

## Complexity theorem

`Target` asserts that this fixed binary language is NP-hard under polynomial-time **many-one** reductions. Use the repository's concrete `NLA.Computation.Complexity.ManyOneNPHard` predicate, which quantifies over actual finite transducer runs and a uniform polynomial bit-time bound. This is a theorem about the unrestricted rational-input language, including the integer subclass used by the cited resolutions. Do not replace it by hardness of bounded feedback, pole assignment, arbitrary bilinear inequalities, or an unspecified reduction relation.

There is no numerical approximation tolerance, probability threshold, or universal analytic constant in this statement. No claim of NP membership or `P ≠ NP` is part of the target. A Lean file may define reusable input/encoding and Hurwitz predicates, but its final `Target` must be this exact NP-hardness assertion and carry the permanent ID `MF-08`.
