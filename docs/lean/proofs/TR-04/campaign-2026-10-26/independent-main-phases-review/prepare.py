#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, shutil, sys

BASE = Path(__file__).resolve().parent
REPO = BASE.parents[5]
PRIOR = BASE.parent / "independent-dimension-review"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
shutil.copyfile(PRIOR / "source_inventory.py", BASE / "source_inventory.py")
sys.path.insert(0, str(BASE))
from source_inventory import declarations_of

specs = [
    ("startup", "tt-startup-author", "00f755e8e5f4aa7f51abb41019e16596fb68306b6bebb4a3ae78b21dacd9577d"),
    ("dispatch_metadata", "header-dispatch-metadata-author", "232f378a6fc5ce0cbbf62b6a2bd22a4a0cf843c3ec33af4c17763af773722069"),
    ("first_selection", "first-selection-author", "da76f2a1fd55054f5ca7120ab3f5733ebce813fead413aa1ab2f8d223e95bc09"),
]


def norm(path):
    return path if path.startswith("lean-statements/") else "lean-statements/" + path


blocks, union = [], {}
for key, directory, digest in specs:
    p = BASE.parent / directory / "source-lock.json"
    assert sha(p) == digest
    d = json.loads(p.read_text())
    records = [dict(r, path=norm(r["path"])) for r in d.get("project_closure", d.get("sources"))]
    for r in records:
        assert sha(REPO / r["path"]) == r["sha256"]
        if r["path"] in union:
            assert union[r["path"]]["sha256"] == r["sha256"]
        union[r["path"]] = r
    owned = d.get("authored_sources", d.get("authored_modules"))
    if isinstance(owned[0], str):
        owned = [r for r in records if Path(r["path"]).stem in owned or r["path"].removeprefix("lean-statements/") in owned]
    else:
        owned = [dict(r, path=norm(r["path"])) for r in owned]
    decls = [v for r in records for v in declarations_of(r["path"].removeprefix("lean-statements/"), (REPO / r["path"]).read_bytes())]
    ownedpaths = {r["path"] for r in owned}
    owneddecls = [v for v in decls if norm(v["source"]) in ownedpaths]
    selected = d.get("authored_declarations", [r["name"] for r in d.get("declarations", [])])
    assert set(selected) <= {v["name"] for v in owneddecls}
    assert all(v["visibility"] in {"public", "private", "local"} for v in decls)
    for v in d.get("unchanged_boundary_and_pins", []):
        assert sha(REPO / v["path"]) == v["sha256"]
    for v in d.get("runtime_pins", []):
        assert sha(REPO / norm(v["path"])) == v["sha256"]
    blocks.append({"key": key, "author_lock_path": str(p.relative_to(REPO)), "author_lock_sha256": digest,
        "author": d["author"], "records": records, "owned": owned, "declarations": decls,
        "owned_declarations": sorted(v["name"] for v in owneddecls),
        "author_selected_public_declarations": selected,
        "roots": d.get("targets", [d.get("target")]),
        "literal_endpoints": [v["name"] for v in owneddecls if v["visibility"] == "public" and v["kind"] in {"theorem", "lemma"}]})
    print(key, len(records), "sources", len(owned), "owned", len(owneddecls), "all named declarations", len(selected), "author-selected public")

private = {}
local = []
for b in blocks:
    for v in b["declarations"]:
        if v["visibility"] == "private":
            module = v["source"].removesuffix(".lean").replace("/", ".")
            private[v["name"]] = {"source": v["source"], "line": v["line"], "module": module,
                "actual_kernel_name": "_private." + module + ".0." + v["name"], "kind": v["kind"]}
        elif v["visibility"] == "local":
            local.append(v)
private_support = REPO.parent / "tooling/lean-4.33.1-darwin_aarch64/src/lean/Lean/PrivateName.lean"
provenance = {"formula": "Lean.mkPrivateNameCore module userName, with exact module+source hash and actual environment lookup required.",
    "compiler_private_name_support": {"path": str(private_support), "sha256": sha(private_support)},
    "private_declarations": private, "local_declarations": local,
    "policy": "No declaration is excluded. Every public/private/local explicit source name receives actual-kind, LeanCert kernel and transitive axiom checks. Private constants must exist at the exact compiler-produced module name; no suffix search or ambiguous fallback is allowed."}
(BASE / "private-name-provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
config = {"reviewer": "/root/recover_verification", "self_authored_proof_sources": [],
    "scope": "Actual finite startup1, dispatch/metadata2, first-SVD selection6. Fresh shared closure with exact public/private/local name checks and separate complete endpoint consumers. No full initialization/recursive program/total cost/Target/Linux/Comparator acceptance claim.",
    "blocks": blocks, "union": list(union.values()), "private_name_map": private,
    "private_name_provenance_sha256": sha(BASE / "private-name-provenance.json"),
    "inventory_helper_provenance": {"path": str((PRIOR / "source_inventory.py").relative_to(REPO)), "sha256": sha(PRIOR / "source_inventory.py"), "change": "Exact copy; no private/local declarations dropped."}}
(BASE / "source-lock.json").write_text(json.dumps(config, indent=2) + "\n")
print("UNION", len(union), "sources; explicit private", len(private), "local", len({v['name'] for v in local}))
