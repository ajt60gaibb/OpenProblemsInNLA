#!/usr/bin/python3 -I
"""Add mount/process/network isolation to Comparator's official Landrun calls.

On the verification host's Landlock ABI 1, Landrun's best-effort handling of
REFER-granting rules disables its entire ruleset. This adapter runs the official
invocation with a read-only host filesystem and exposes only
the build's .lake directory for writes. Exports receive no writable .lake mount.
The /dev and /proc mounts, process tree, IPC and network are private; capabilities
are dropped. The outer systemd service also restricts AF_UNIX socket creation.

This adapter supports the arguments emitted by the bundled Comparator and
rejects unexpected options or writable paths.
"""

import os
from pathlib import Path
import sys


def main() -> None:
    landrun = Path(__file__).resolve().parents[1] / ".tools/bin/landrun"
    workdir = Path.cwd().resolve()
    arguments = sys.argv[1:]
    writable_build = None
    index = 0
    while index < len(arguments):
        option = arguments[index]
        if option == "--":
            if index + 1 == len(arguments):
                raise ValueError("missing sandbox command")
            break
        if option in {"--best-effort", "-ldd", "-add-exec"}:
            index += 1
            continue
        if option not in {"--ro", "--rox", "--rw", "--rwx", "--env"}:
            raise ValueError(f"unsupported Comparator Landrun option: {option}")
        if index + 1 == len(arguments):
            raise ValueError(f"missing value for {option}")
        value = arguments[index + 1]
        if option == "--rw":
            if value != "/dev":
                raise ValueError("only private /dev may be passed with --rw")
        elif option == "--rwx":
            path = Path(value)
            expected = workdir / ".lake"
            if path != expected or path.is_symlink() or not path.is_dir():
                raise ValueError("only this project's existing .lake may be writable")
            writable_build = path
        index += 2
    else:
        raise ValueError("missing explicit command separator")

    if not landrun.is_file() or not os.access(landrun, os.X_OK):
        raise ValueError(f"official Landrun executable missing: {landrun}")
    command = [
        "/usr/bin/bwrap", "--unshare-all", "--die-with-parent", "--new-session",
        "--cap-drop", "ALL", "--ro-bind", "/", "/", "--proc", "/proc",
        "--dev", "/dev", "--chdir", str(workdir),
    ]
    if writable_build is not None:
        command += ["--bind", str(writable_build), str(writable_build)]
    command += ["--", str(landrun), *arguments]
    os.execv(command[0], command)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        print(f"strict Comparator sandbox: {error}", file=sys.stderr)
        sys.exit(2)
