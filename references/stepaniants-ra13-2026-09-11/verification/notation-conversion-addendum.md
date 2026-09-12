# RA-13 independent review addendum: notation corrections

Reviewer: Codex agent `/root/review_aa01`  
Date: 11 September 2026  
Outcome: **PASS for the two identified notation corrections.** The original signed review remains unchanged.

This addendum is bound to:

- The frozen 14,786-byte proof `/tmp/nla-fresh-round1/ra13/full-proof-candidate.md`, SHA-256 `6ee4efe2bf23c91276db20bb2bf67ca05c5fa659f30f50b6f8670fd8507d5dff`.
- The 12,052-byte independent review `/tmp/nla-fresh-round1/ra13/independent-review-aa01.md`, SHA-256 `86f795530bec85ac00e93c6a1fd88b0a2985d49ac38606c2db3c5662b7784b99`.

## Corrections checked directly against the frozen text

1. In the Section 3 display defining M,V,R, replace the two literal `,quad` strings by `,\quad`. These are missing LaTeX command backslashes; the three definitions and their meanings remain unchanged.
2. In the following Section 3 display, change only the leading `u(t)` in `u(t)=1-g(z-t)/g(z)\ge0.` to `\nu(t)`. Every subsequent kernel integral, the definition of the auxiliary measure's masses, and the original signed independent review use the symbol ν for this same nonnegative function. There is no other definition or use that requires a separate Latin-u function. The corrected definition is exactly the function independently audited in the original review.

Both corrections repair notation; they alter no inequality, parameter, assumption, derivative identity, or proof step. In particular, ν(t) remains the bounded nonnegative function obtained from the global maximum of g, and is the same function integrated in A0, B0, and C0. The full mathematical PASS in the original review is unaffected.

The frozen reviewed source and the signed review should be preserved byte-for-byte. The permitted corrections may be applied to the canonical publication source. This addendum alone does not certify arbitrary additional manuscript edits or the final rendered PDF; an exact comparison with the final publication files is a separate check.
