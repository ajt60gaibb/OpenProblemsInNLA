#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, shutil, sys

BASE = Path(__file__).resolve().parent
REPO = BASE.parents[5]
PRIOR = BASE.parent / "independent-main-phases-review"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
shutil.copyfile(PRIOR / "source_inventory.py", BASE / "source_inventory.py")
helper = BASE / "source_inventory.py"
helper_text = helper.read_text()
original_qualification = "'name': prefix + '.' + declaration"
assert helper_text.count(original_qualification) == 1
helper.write_text(helper_text.replace(original_qualification, "'name': (prefix + '.' + declaration) if prefix else declaration"))
sys.path.insert(0, str(BASE))
from source_inventory import declarations_of

specs = [
    ("first_context", "tt-first-loop-context-author", "533408235022130adcb332eb20d0012bc480aa87223edc547978bb640b0bdbd3"),
    ("minimum_strict", "minimum-strict-author", "fe309587f5c9a35b7fcb523c3f2b936274b067a2fdec1fe8f8e05d6d7a8a4e1c"),
    ("store_context", "store-context-author", "264404bb35103ea8ce3973416107b035e7ba54cfcf8c0e623726a5edef4113b6"),
    ("recursive_execution", "tt-recursive-execution-author", "ff4af80bbb0ed11ca5065750f816b00d781b2b5ab2a959610a3841b24c668495"),
    ("final_context", "final-context-author", "d8b1d2d083113e4d55eece983725c628b604edb9cdac35f9942b0b4c95da1969"),
    ("full_target", "tt-full-target-author", "dc7d3893866dd89b2cd5413248ebbf86fc5a37e0bbcd37ad74514ccb8e85eb53")]



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
    author_record_count = len(records)
    reviewer_extra_sources = []
    if key == "full_target":
        # Rebuild the original frozen mirror as reviewer evidence and actually
        # prove the rfl identity, beyond merely reading the Target alias.
        extra = {"path": "lean-statements/Reviewed/TR04.lean",
            "sha256": sha(REPO / "lean-statements/Reviewed/TR04.lean"),
            "bytes": (REPO / "lean-statements/Reviewed/TR04.lean").stat().st_size}
        assert extra["sha256"] == "5b2260e25e8ce7dda5455a3cf11a5c16fc2493ce3d0cf1ab84a447d2fb1f54cd"
        records.append(extra)
        union[extra["path"]] = extra
        reviewer_extra_sources.append(extra)
    owned = d.get("authored_sources", d.get("authored_modules"))
    if isinstance(owned[0], str):
        owned = [r for r in records if Path(r["path"]).stem in owned or r["path"].removeprefix("lean-statements/") in owned]
    else:
        owned = [dict(r, path=norm(r["path"])) for r in owned]
    decls = [v for r in records for v in declarations_of(r["path"].removeprefix("lean-statements/"), (REPO / r["path"]).read_bytes())]
    for v in decls:
        module = v["source"].removesuffix(".lean").replace("/", ".")
        v["audit_id"] = "_private." + module + ".0." + v["name"] if v["visibility"] == "private" else v["name"]
    assert len({v["audit_id"] for v in decls}) == len(decls), "Duplicate actual kernel identity"
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
        "owned_declarations": sorted(v["audit_id"] for v in owneddecls), "owned_source_names": sorted(v["name"] for v in owneddecls),
        "author_selected_public_declarations": selected,
        "roots": d.get("targets", [d.get("target")]) + (["Reviewed.TR04"] if key == "full_target" else []),
        "author_record_count": author_record_count, "reviewer_extra_sources": reviewer_extra_sources,
        "literal_endpoints": [v["name"] for v in owneddecls if v["visibility"] == "public" and v["kind"] in {"theorem", "lemma"}]})
    print(key, len(records), "sources", len(owned), "owned", len(owneddecls), "all named declarations", len(selected), "author-selected public")

private = {}
local = []
for b in blocks:
    for v in b["declarations"]:
        if v["visibility"] == "private":
            module = v["source"].removesuffix(".lean").replace("/", ".")
            private[v["audit_id"]] = {"source_name": v["name"], "source": v["source"], "line": v["line"], "module": module,
                "actual_kernel_name": "_private." + module + ".0." + v["name"], "kind": v["kind"]}
        elif v["visibility"] == "local":
            local.append(v)
private_support = REPO.parent / "tooling/lean-4.33.1-darwin_aarch64/src/lean/Lean/PrivateName.lean"
provenance = {"formula": "Lean.mkPrivateNameCore module userName, with exact module+source hash and actual environment lookup required.",
    "compiler_private_name_support": {"path": str(private_support), "sha256": sha(private_support)},
    "private_declarations": private, "local_declarations": local,
    "policy": "Private identities are keyed by exact module-qualified compiler names, so same source-user names in different modules remain distinct. No declaration is excluded. Every public/private/local explicit source name receives actual-kind, LeanCert kernel and transitive axiom checks. Private constants must exist at the exact compiler-produced module name; no suffix search or ambiguous fallback is allowed."}
(BASE / "private-name-provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
config = {"reviewer": "/root/recover_verification", "self_authored_proof_sources": [],
    "scope": "Frozen first-context4, minimum-strict2, store-context1, recursive-execution11, final-context1 and complete-root-Target6, exact public/private name checks and independent fresh shared184-source (including one reviewer-added frozen Reviewed mirror) closure. This lock is preparation only; terminal independent Target acceptance requires every author terminal receipt, complete fresh replay and immutable original statement checks. No authoritative Linux/Comparator or canonical publication acceptance from this source audit.",
    "blocks": blocks, "union": list(union.values()), "private_name_map": private,
    "private_name_provenance_sha256": sha(BASE / "private-name-provenance.json"),
    "inventory_helper_provenance": {"path": str((PRIOR / "source_inventory.py").relative_to(REPO)), "sha256": sha(PRIOR / "source_inventory.py"), "change": "Retain every original namespaced declaration; qualify empty-namespace global declarations without a leading dot. No private/local declarations dropped."}}
(BASE / "source-lock.json").write_text(json.dumps(config, indent=2) + "\n")
print("UNION", len(union), "sources; explicit private", len(private), "local", len({v['name'] for v in local}))
