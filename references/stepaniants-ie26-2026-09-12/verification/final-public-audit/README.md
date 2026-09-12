# Final public-network eligibility check: MF-02 and IE-26

Checked at **2026-09-12 02:10:34 UTC**. The [sanitized record](network-check-sanitized.json) binds all five repositories, 40 public branch heads, 38 unique trees and 108 unique selected text blobs. The audit also read all issue/PR bodies and comments in those repositories, and all PR-review bodies, filtering for both IDs and related cubic/sign/Fourier/interpolation terms. The only matching discussion was the admission PR for IE-26; it contains no solution to either target.

MF-02 is marked Open at every head. IE-26 is Open at 11 heads and absent at 29 older heads. Both remain Open on upstream main `1f22006bdaa4659fcaa0bb775a887685cd3cc566`. No competing full resolution was located. This is a bounded public-network check, not a certification about private, deleted, unpublished or unidentifiably named work, nor a novelty determination. MF-02's prior-publication synthesis and credit are assessed separately in its source review.

The run reused previously fetched immutable Git blobs by their exact SHA; branch inventories, trees and discussions were fetched afresh. The record binds the two earlier private snapshots by checksum and date. It contains no contact addresses, raw discussion bodies or copied publication text. Raw snapshots stay private.

Reproduce a fresh public check with authenticated GitHub CLI:

```bash
GH=/path/to/gh python3 audit_public.py --output /tmp/public-network.json
```

Optional `--cache-snapshot /path/to/earlier-full-snapshot.json` arguments reuse immutable blob text by SHA only. The portable script differs from the exact run script only by making those optional cache paths command-line arguments; both fingerprints are recorded. Future runs naturally reflect changed public state.
