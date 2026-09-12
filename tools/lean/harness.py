#!/usr/bin/env python3
"""Reproduce the pinned Forsythe Comparator tools against a fresh NLA project.

SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 George Stepaniants.

The proof checker, strict sandbox and preserved probes are fetched verbatim
from the SHA256-locked Apache/MIT sources described in NOTICE.md. This driver
generalizes project selection and records fresh results; it does not certify
the English-to-Lean correspondence or substitute for independent referees.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.parse
import urllib.request


ROOT = Path(__file__).resolve().parent
LOCK = ROOT / "source-lock.json"
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
SHA = re.compile(r"[0-9a-f]{40}\Z")


class HarnessError(Exception):
    """An unmet verification precondition; never a theorem rejection."""


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path: Path) -> dict:
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise HarnessError(f"duplicate JSON key in {path}: {key}")
            result[key] = value
        return result
    result = json.loads(path.read_text(), object_pairs_hook=unique)
    if not isinstance(result, dict):
        raise HarnessError(f"expected a JSON object: {path}")
    return result


def regular_path(path: Path) -> Path:
    absolute = path.absolute()
    for part in [absolute, *absolute.parents]:
        if part.is_symlink():
            raise HarnessError(f"symbolic-link path is not allowed: {part}")
    return absolute.resolve()


def relative_file(value: str) -> PurePosixPath:
    result = PurePosixPath(value)
    if (not value or result.is_absolute() or str(result) != value
            or any(p in {"", ".", ".."} for p in result.parts)
            or "\\" in value or any(ord(c) < 32 for c in value)):
        raise HarnessError(f"invalid relative source path: {value!r}")
    return result


def load_lock() -> dict:
    lock = read_json(LOCK)
    if (lock.get("schema_version") != 1
            or lock.get("repository") != "https://github.com/sgstepaniants/Forsythe"
            or not SHA.fullmatch(lock.get("commit", ""))
            or lock.get("lean_toolchain") != "leanprover/lean4:v4.33.1"):
        raise HarnessError("unsupported or malformed source-lock.json")
    destinations = set()
    for entry in lock["files"]:
        relative_file(entry["source"])
        destination = relative_file(entry["destination"])
        if str(destination) in destinations:
            raise HarnessError(f"duplicate locked source: {destination}")
        destinations.add(str(destination))
        if not re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]):
            raise HarnessError("invalid source digest")
    return lock


def linux_requirements() -> None:
    if platform.system() != "Linux":
        raise HarnessError("authoritative Comparator verification requires Linux; "
                           "macOS builds are not a substitute and fake-landrun is forbidden")
    if os.getuid() == 0:
        raise HarnessError("run the verifier as a non-root Linux user")
    for name in ["git", "python3", "systemd-run"]:
        if not shutil.which(name):
            raise HarnessError(f"missing prerequisite: {name}")
    if not Path("/usr/bin/bwrap").is_file():
        raise HarnessError("missing /usr/bin/bwrap (Bubblewrap)")


def clean_environment() -> dict[str, str]:
    # No credentials are read, copied, or passed through the environment.
    allowed = ("PATH", "HOME", "LANG", "LC_ALL", "TERM", "XDG_RUNTIME_DIR",
               "DBUS_SESSION_BUS_ADDRESS", "ELAN_HOME", "SSL_CERT_FILE", "SSL_CERT_DIR")
    env = {key: os.environ[key] for key in allowed if key in os.environ}
    env.update({"GIT_TERMINAL_PROMPT": "0", "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_CONFIG_GLOBAL": "/dev/null"})
    return env


def command(args: list[str], *, cwd: Path | None = None,
            env: dict[str, str] | None = None) -> str:
    result = subprocess.run(args, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
    if result.returncode:
        raise HarnessError(f"command failed ({result.returncode}): {shlex.join(args)}\n"
                           f"{result.stderr.strip()}")
    return result.stdout.strip()


def logged(args: list[str], logfile: Path, *, cwd: Path,
           env: dict[str, str], expected: int = 0, markers: tuple[str, ...] = ()) -> str:
    logfile.parent.mkdir(parents=True, exist_ok=True)
    print(f"Running {shlex.join(args)}\nLog: {logfile}", flush=True)
    chunks = []
    with logfile.open("w") as stream:
        stream.write(f"$ {shlex.join(args)}\n")
        stream.flush()
        process = subprocess.Popen(args, cwd=cwd, env=env, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert process.stdout is not None
        for line in process.stdout:
            stream.write(line)
            stream.flush()
            print(line, end="", flush=True)
            chunks.append(line)
        status = process.wait()
        stream.write(f"\nEXIT_STATUS={status}\n")
    output = "".join(chunks)
    if status != expected or any(marker not in output for marker in markers):
        raise HarnessError(f"verification phase failed: {logfile} (exit {status}, "
                           f"expected {expected}; required markers {markers})")
    return output


def verify_sources(tool_dir: Path, lock: dict) -> None:
    for entry in lock["files"]:
        path = regular_path(tool_dir / entry["destination"])
        if (not path.is_file() or path.stat().st_size != entry["bytes"]
                or digest(path) != entry["sha256"]):
            raise HarnessError(f"missing or modified pinned verification source: {path}")


def fetch_sources(tool_dir: Path, lock: dict) -> None:
    def fetch(entry: dict) -> None:
        target = regular_path(tool_dir / entry["destination"])
        if target.exists():
            if target.stat().st_size == entry["bytes"] and digest(target) == entry["sha256"]:
                return
            raise HarnessError(f"refusing to overwrite modified source: {target}")
        url = ("https://raw.githubusercontent.com/sgstepaniants/Forsythe/"
               + lock["commit"] + "/" + entry["source"])
        data = urllib.request.urlopen(url, timeout=60).read()
        if len(data) != entry["bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
            raise HarnessError(f"source digest mismatch: {url}")
        target.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=target.parent, delete=False) as temporary:
            temporary.write(data)
            temporary_path = Path(temporary.name)
        temporary_path.replace(target)
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        list(pool.map(fetch, lock["files"]))
    for entry in lock["files"]:
        path = tool_dir / entry["destination"]
        if path.suffix in {".sh", ".py"}:
            path.chmod(0o755)
    verify_sources(tool_dir, lock)


def tool_environment(tool_dir: Path, receipt: dict) -> dict[str, str]:
    env = clean_environment()
    env["PATH"] = str(Path(receipt["lean_prefix"]) / "bin") + ":" + env.get("PATH", "")
    env.update({"COMPARATOR_BIN": str(tool_dir / ".tools/comparator/.lake/build/bin/comparator"),
                "COMPARATOR_LEAN4EXPORT": str(tool_dir / ".tools/lean4export/.lake/build/bin/lean4export"),
                "COMPARATOR_LANDRUN": str(tool_dir / "scripts/strict_landrun.py"),
                "XDG_CACHE_HOME": str(tool_dir / ".tools/cache"),
                "TMPDIR": str(tool_dir / ".verification-tmp")})
    return env


def bootstrap(tool_dir: Path) -> None:
    linux_requirements()
    for name in ["elan", "go", "cc"]:
        if not shutil.which(name):
            raise HarnessError(f"bootstrap requires {name}; Go must be at least 1.24")
    tool_dir = regular_path(tool_dir)
    tool_dir.mkdir(parents=True, exist_ok=True)
    lock = load_lock()
    logdir = tool_dir / "logs/bootstrap"
    env = clean_environment()
    fetch_sources(tool_dir, lock)
    (tool_dir / ".verification-tmp").mkdir(exist_ok=True)
    (tool_dir / ".tools/bin").mkdir(exist_ok=True)
    (tool_dir / ".tools/cache").mkdir(exist_ok=True)
    logged(["elan", "toolchain", "install", lock["lean_toolchain"]],
           logdir / "elan.log", cwd=tool_dir, env=env)
    prefix = command(["elan", "run", lock["lean_toolchain"], "lean", "--print-prefix"], env=env)
    lean_version = command([str(Path(prefix) / "bin/lean"), "--version"], env=env)
    if not re.search(r"version 4\.33\.1(?:\D|$)", lean_version):
        raise HarnessError(f"unexpected Lean version: {lean_version}")
    go_version = command(["go", "version"], env=env)
    go_match = re.search(r"go(\d+)\.(\d+)", go_version)
    if not go_match or tuple(map(int, go_match.groups())) < (1, 24):
        raise HarnessError(f"Go >=1.24 required; found {go_version}")
    env.update({"PATH": str(Path(prefix) / "bin") + ":" + env["PATH"],
                "GOTOOLCHAIN": "local", "GOPATH": str(tool_dir / ".tools/go-work"),
                "GOCACHE": str(tool_dir / ".tools/go-cache")})
    logged(["go", "build", "-mod=readonly", "-buildvcs=false", "-o",
            str(tool_dir / ".tools/bin/landrun"), "./cmd/landrun"],
           logdir / "landrun-build.log", cwd=tool_dir / ".tools/landrun", env=env)
    logged(["lake", "build", "lean4export", "comparator"],
           logdir / "comparator-build.log", cwd=tool_dir / ".tools/comparator", env=env)
    verify_sources(tool_dir, lock)
    receipt = {"source_lock_sha256": digest(LOCK), "forsythe_commit": lock["commit"],
               "lean_toolchain": lock["lean_toolchain"], "lean_prefix": prefix,
               "lean_version": lean_version, "go_version": go_version,
               "platform": platform.platform(), "executables": {}}
    for name in [".tools/comparator/.lake/build/bin/comparator",
                 ".tools/lean4export/.lake/build/bin/lean4export", ".tools/bin/landrun"]:
        receipt["executables"][name] = digest(tool_dir / name)
    runenv = tool_environment(tool_dir, receipt)
    envfile = tool_dir / ".tools/env.sh"
    # The unchanged Forsythe probes source this file. Values are shell-quoted.
    probe_keys = {"PATH", "COMPARATOR_BIN", "COMPARATOR_LEAN4EXPORT", "COMPARATOR_LANDRUN",
                  "XDG_CACHE_HOME", "TMPDIR"}
    envfile.write_text("# Generated by the NLA pinned-tool bootstrap.\n" + "\n".join(
        f"export {key}={shlex.quote(value)}" for key, value in runenv.items()
        if key in probe_keys) + "\n")
    receipt["env_sha256"] = digest(envfile)
    (tool_dir / "bootstrap.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"Tools built; isolation and checker controls run during verify. Receipt: {tool_dir / 'bootstrap.json'}")


def validate_project(project: Path) -> dict:
    if (project / "lakefile.lean").exists() or not (project / "lakefile.toml").is_file():
        raise HarnessError("initial harness requires exactly one lakefile.toml and no lakefile.lean")
    manifest = read_json(project / "lake-manifest.json")
    if manifest.get("packagesDir") != ".lake/packages":
        raise HarnessError("lake-manifest.json must use contained .lake/packages")
    for package in manifest.get("packages", []):
        parsed = urllib.parse.urlsplit(package.get("url", ""))
        if (package.get("type") != "git" or not SHA.fullmatch(package.get("rev", ""))
                or parsed.scheme != "https" or parsed.netloc != "github.com"
                or parsed.query or parsed.fragment):
            raise HarnessError("dependencies must be immutable HTTPS GitHub git revisions; "
                               "path, credential-bearing and floating dependencies are unsupported")
    config = read_json(project / "comparator.json")
    required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
    if set(config) - required - {"definition_names"} or not required <= set(config):
        raise HarnessError("unsupported Comparator config keys")
    if config.get("definition_names", []):
        raise HarnessError("definition holes require a separately reviewed harness extension")
    challenge, solution = config["challenge_module"], config["solution_module"]
    if (not isinstance(challenge, str) or not MODULE.fullmatch(challenge)
            or not isinstance(solution, str) or not MODULE.fullmatch(solution) or challenge == solution):
        raise HarnessError("Challenge and Solution must name distinct Lean modules")
    names = config["theorem_names"]
    if (not isinstance(names, list) or not names
            or any(not isinstance(n, str) or not MODULE.fullmatch(n) for n in names)
            or len(set(names)) != len(names)):
        raise HarnessError("theorem_names must contain distinct qualified Lean names")
    axioms = config["permitted_axioms"]
    if (not isinstance(axioms, list) or any(not isinstance(a, str) for a in axioms)
            or len(set(axioms)) != len(axioms) or not set(axioms) <= STANDARD_AXIOMS):
        raise HarnessError("only propext, Quot.sound and Classical.choice may be permitted")
    return config


def snapshot(project: Path, destination: Path) -> tuple[dict, dict[str, str]]:
    repo = Path(command(["git", "rev-parse", "--show-toplevel"], cwd=project))
    relative = project.relative_to(repo).as_posix()
    if relative == ".":
        raise HarnessError("select a self-contained Lean project below the repository root")
    command(["git", "diff", "--exit-code", "HEAD", "--", relative], cwd=repo)
    commit = command(["git", "rev-parse", "HEAD"], cwd=repo)
    tree = subprocess.check_output(["git", "ls-tree", "-r", "-z", commit, "--", relative], cwd=repo)
    hashes = {}
    for entry in tree.split(b"\0"):
        if not entry:
            continue
        metadata, rawname = entry.split(b"\t", 1)
        mode, kind, object_id = metadata.decode().split()
        if mode not in {"100644", "100755"} or kind != "blob":
            raise HarnessError("project snapshots must contain only ordinary tracked files")
        name = rawname.decode()
        local = PurePosixPath(name).relative_to(relative)
        if ".lake" in local.parts or local.suffix in {".olean", ".ilean", ".o", ".so", ".a"}:
            raise HarnessError(f"tracked build artifact forbidden: {name}")
        data = subprocess.check_output(["git", "cat-file", "blob", object_id], cwd=repo)
        target = destination.joinpath(*local.parts)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        target.chmod(0o755 if mode == "100755" else 0o644)
        hashes[str(local)] = hashlib.sha256(data).hexdigest()
    return {"repository_commit": commit, "project": relative}, hashes


def unchanged(project: Path, hashes: dict[str, str]) -> None:
    for name, expected in hashes.items():
        file = regular_path(project / name)
        if not file.is_file() or digest(file) != expected:
            raise HarnessError(f"trusted input changed during verification: {name}")


def systemd(args: list[str], cwd: Path, env: dict[str, str]) -> list[str]:
    # --pipe supports noninteractive CI and propagates the service exit code.
    exports = [f"{key}={value}" for key, value in env.items()]
    return ["systemd-run", "--user", "--quiet", "--wait", "--pipe", "--collect",
            "-p", "RestrictAddressFamilies=~AF_UNIX", "--working-directory", str(cwd),
            "/usr/bin/env", "-i", *exports, *args]


def extra_regressions(tool_dir: Path, logdir: Path, env: dict[str, str]) -> None:
    # These are checker fixtures, not NLA mathematical results.
    for case, statement, honest_proof, proof, marker in [
        ("sorry", "(1 : Nat) = 1", "rfl", "sorry", "Illegal axiom detected: 'sorryAx'"),
        # Lean 4.33.1 creates a fresh named axiom rather than using the older
        # generic Lean.ofReduceBool. #print axioms was checked for this fixture.
        ("native", "(List.range 37).reverse.length = 37", "decide", "native_decide",
         "Illegal axiom detected: 'checked._native.native_decide.ax_1_1'")]:
        with tempfile.TemporaryDirectory(prefix="nla-axiom-", dir=env["TMPDIR"]) as name:
            project = Path(name)
            (project / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
            (project / "lakefile.toml").write_text(
                'name = "NlaAxiomFixture"\n[[lean_lib]]\nname = "Challenge"\n'
                '[[lean_lib]]\nname = "Solution"\n')
            (project / "Challenge.lean").write_text(
                f"import Lean\ntheorem checked : {statement} := by {honest_proof}\n")
            (project / "Solution.lean").write_text(
                f"import Lean\ntheorem checked : {statement} := by {proof}\n")
            (project / "comparator.json").write_text(json.dumps({
                "challenge_module": "Challenge", "solution_module": "Solution",
                "theorem_names": ["checked"], "permitted_axioms": sorted(STANDARD_AXIOMS)}))
            args = systemd(["lake", "env", env["COMPARATOR_BIN"], "comparator.json"], project, env)
            logged(args, logdir / f"negative-{case}.log", cwd=project, env=env,
                   expected=1, markers=("Building Challenge", "Building Solution", marker))


def validated_tools(tool_dir: Path) -> tuple[dict, dict[str, str]]:
    linux_requirements()
    lock = load_lock()
    verify_sources(tool_dir, lock)
    receipt = read_json(tool_dir / "bootstrap.json")
    if receipt["source_lock_sha256"] != digest(LOCK):
        raise HarnessError("tool bootstrap used a different source lock")
    if set(receipt["executables"]) != {".tools/comparator/.lake/build/bin/comparator",
                                       ".tools/lean4export/.lake/build/bin/lean4export",
                                       ".tools/bin/landrun"}:
        raise HarnessError("bootstrap receipt does not enumerate the expected tool binaries")
    for name, expected in receipt["executables"].items():
        file = regular_path(tool_dir / relative_file(name))
        if digest(file) != expected:
            raise HarnessError(f"modified checker executable: {file}")
    if digest(tool_dir / ".tools/env.sh") != receipt["env_sha256"]:
        raise HarnessError("modified probe environment file")
    env = tool_environment(tool_dir, receipt)
    if command(["lean", "--version"], env=env) != receipt["lean_version"]:
        raise HarnessError("Lean toolchain differs from the bootstrap receipt")
    return receipt, env


def run_controls(tool_dir: Path, logdir: Path, env: dict[str, str]) -> None:
    # Fail before any solution work if this Linux host cannot supply the real sandbox.
    logged(["python3", str(tool_dir / "reproduction/checks/sandbox_probe.py")],
           logdir / "sandbox.log", cwd=tool_dir, env=env)
    logged(["bash", str(tool_dir / "reproduction/checks/run_replay.sh")],
           logdir / "kernel-controls.log", cwd=tool_dir, env=env,
           markers=("PASS: all three actual Comparator.runBuiltinKernel cases behaved as required",))
    logged(["python3", str(tool_dir / "reproduction/checks/comparator_regressions.py")],
           logdir / "comparator-controls.log", cwd=tool_dir, env=env,
           markers=("PASS: all five Comparator regressions",))
    extra_regressions(tool_dir, logdir, env)


def new_logdir(tool_dir: Path, phase: str) -> Path:
    logdir = tool_dir / "logs" / (time.strftime(phase + "-%Y%m%dT%H%M%SZ", time.gmtime()) + f"-{os.getpid()}")
    logdir.mkdir(parents=True)
    return logdir


def selftest(tool_dir: Path) -> None:
    linux_requirements()
    tool_dir = regular_path(tool_dir)
    receipt, env = validated_tools(tool_dir)
    logdir = new_logdir(tool_dir, "selftest")
    run_controls(tool_dir, logdir, env)
    (logdir / "result.json").write_text(json.dumps({
        "result": "checker-selftest-passed", "tool_receipt": receipt,
        "mathematical_verification": "none; checker fixtures only"}, indent=2) + "\n")
    print(f"PASS: sandbox and checker controls only. Evidence: {logdir}")


def verify(project: Path, tool_dir: Path) -> None:
    linux_requirements()
    project, tool_dir = regular_path(project), regular_path(tool_dir)
    lock = load_lock()
    receipt, env = validated_tools(tool_dir)
    logdir = new_logdir(tool_dir, "verify")
    run_controls(tool_dir, logdir, env)
    with tempfile.TemporaryDirectory(prefix="nla-fresh-proof-", dir=env["TMPDIR"]) as temporary:
        fresh = Path(temporary) / "project"
        fresh.mkdir()
        provenance, hashes = snapshot(project, fresh)
        config = validate_project(fresh)
        if (fresh / "lean-toolchain").read_text().strip() != lock["lean_toolchain"]:
            raise HarnessError("project toolchain must match the pinned verifier: " + lock["lean_toolchain"])
        # Materialize exact public dependencies; no Solution build precedes Comparator.
        logged(["lake", "env", "true"], logdir / "dependencies.log", cwd=fresh, env=env)
        unchanged(fresh, hashes)
        if os.environ.get("NLA_LEAN_SKIP_CACHE") != "1":
            logged(["lake", "exe", "cache", "get"], logdir / "mathlib-cache.log", cwd=fresh, env=env)
            unchanged(fresh, hashes)
        args = systemd(["lake", "env", env["COMPARATOR_BIN"], "comparator.json"], fresh, env)
        logged(args, logdir / "comparator.log", cwd=fresh, env=env,
               markers=("Lean default kernel accepts the solution", "Your solution is okay!"))
        unchanged(fresh, hashes)
        result = {**provenance, "config": config, "input_sha256": hashes,
                  "source_lock_sha256": digest(LOCK), "tool_receipt": receipt,
                  "result": "comparator-accepted", "semantic_review": "not-performed-by-this-command"}
        (logdir / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS: fresh Comparator run and all controls. Evidence: {logdir}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="action", required=True)
    install = commands.add_parser("bootstrap")
    install.add_argument("tool_dir", type=Path)
    controls = commands.add_parser("selftest")
    controls.add_argument("tool_dir", type=Path)
    check = commands.add_parser("verify")
    check.add_argument("project", type=Path)
    check.add_argument("tool_dir", type=Path)
    args = parser.parse_args()
    try:
        if args.action == "bootstrap":
            bootstrap(args.tool_dir)
        elif args.action == "selftest":
            selftest(args.tool_dir)
        else:
            verify(args.project, args.tool_dir)
        return 0
    except (HarnessError, OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print(f"Lean verification precondition/check failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
