#!/usr/bin/env python3
"""Freshly typecheck locked IE22 signatures; deliberate holes are not proofs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

def sha(data):
    return hashlib.sha256(data).hexdigest()

def imports(data):
    for line in data.decode().splitlines():
        match = re.match(r"\s*(?:public\s+)?import\s+(.+)", line)
        if match:
            for name in match[1].split("--", 1)[0].split():
                if re.fullmatch(r"[\w.]+", name):
                    yield name

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--packages", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    packet = Path(__file__).resolve().parent
    lock = json.loads((packet / "INPUT_LOCK.json").read_text())
    for name, digest in lock["packet_files"].items():
        assert sha((packet / name).read_bytes()) == digest, name
    locked = {item["path"]: item for item in lock["reviewed_inputs"]}
    for path, item in locked.items():
        assert sha((packet / "frozen" / path).read_bytes()) == item["sha256"], path
    args.output.mkdir(parents=True, exist_ok=False)
    source_root = args.output / "source"
    output_root = args.output / "out"
    logs = args.output / "logs"
    for path in [source_root, output_root, logs]:
        path.mkdir()
    sources = {}
    order = []
    active = set()
    def visit(module):
        if module in sources:
            return
        relative = "lean-statements/" + module.replace(".", "/") + ".lean"
        if not module.startswith(("NLA.", "Reviewed.")):
            return
        assert relative in locked, relative
        assert module not in active, module
        active.add(module)
        data = (packet / "frozen" / relative).read_bytes()
        for child in imports(data):
            visit(child)
        active.remove(module)
        sources[module] = data
        order.append(module)
    challenge = (packet / "Challenge.lean").read_bytes()
    for module in imports(challenge):
        visit(module)
    sources["Challenge"] = challenge
    order.append("Challenge")
    for module, data in sources.items():
        path = source_root / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    env = os.environ.copy()
    dependencies = sorted(p / ".lake/build/lib/lean" for p in args.packages.iterdir()
                          if (p / ".lake/build/lib/lean").is_dir())
    env["LEAN_PATH"] = ":".join(map(str, [output_root] + dependencies +
                                [args.lean.parent.parent / "lib/lean"]))
    result = {"scope": "Statement typecheck only; three deliberate reference holes are not proofs",
              "base": lock["published_base"], "challenge_sha256": sha(challenge),
              "sources": {name: sha(data) for name, data in sources.items()},
              "commands": [], "passed": False}
    for module in order:
        path = source_root / (module.replace(".", "/") + ".lean")
        obj = output_root / (module.replace(".", "/") + ".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        argv = [str(args.lean), "-R", str(source_root), "-o", str(obj), str(path)]
        proc = subprocess.run(argv, cwd=source_root, env=env, capture_output=True,
                              text=True, timeout=300)
        log = logs / (module + ".log")
        log.write_text(proc.stdout + proc.stderr)
        result["commands"].append({"module": module, "argv": argv,
                                   "exit_code": proc.returncode, "log_sha256": sha(log.read_bytes())})
        print(module, proc.returncode, flush=True)
        if proc.returncode:
            print(proc.stdout + proc.stderr, flush=True)
            break
    result["passed"] = len(result["commands"]) == len(order) and all(
        item["exit_code"] == 0 for item in result["commands"])
    (args.output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    raise SystemExit(0 if result["passed"] else 1)

if __name__ == "__main__":
    main()
