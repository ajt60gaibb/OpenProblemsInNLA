# Reproduce the descriptive promotion review

The exact v1 and v2 packet bytes are retained under their respective `frozen-proposal/` directories. The script reads immutable Git objects, overlays only proposed descriptive files in memory, verifies lock entries and unchanged source/runtime copies, checks both source/package approval scopes, and verifies the independently sealed candidate Linux review manifest and accepted result.

```sh
python3 review_promotion.py \
  --repo /path/to/Git-containing-exact-source-and-review-commits \
  --proposal /path/to/immutable-proposal-v2 \
  --output /path/to/new-review-output \
  --linux-review /path/to/sealed/re06-linux-review/crosscheck-v2
```

The script's v2 comparison also uses the adjacent preserved `v1/frozen-proposal` to check the explicit same-byte correction boundary. Original source and package approvals are read from the repository's separately sealed review directories; the other complete-source approval is read from exact Git `baad44b0dc1e0facf9a8824f78c4f69efa47129f`. Their bound receipt copies are retained under `v2/gate-receipts`.

The separate schema-validation receipt documents the actual pinned validator invocation against a private 295-input metadata overlay. It does not modify the proposal or any worktree. No mathematical rebuild, new Linux run, final promoted receipt, or additional Comparator execution is claimed by this promotion reader.
