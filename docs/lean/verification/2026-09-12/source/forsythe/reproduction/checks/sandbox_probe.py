from pathlib import Path
import errno
import os
import socket
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
ADAPTER = ROOT / "scripts/strict_landrun.py"


def child() -> int:
    fixture = Path(sys.argv[2])
    build = sys.argv[3] == "build"
    host_pid = int(sys.argv[4])
    host_port = int(sys.argv[5])
    expected_namespaces = dict(item.split("=", 1) for item in sys.argv[6:])
    failures = []

    def expect_denied(label, operation, allowed_errors):
        try:
            result = operation()
            if isinstance(result, int):
                os.close(result)
        except OSError as error:
            if error.errno in allowed_errors:
                print(f"PASS {label}: denied errno={error.errno}", flush=True)
                return
            failures.append(f"{label}: unexpected errno={error.errno}")
            return
        failures.append(f"{label}: unexpectedly allowed")

    expect_denied("outside .lake write-open", lambda: os.open(fixture / "outside-write.txt", os.O_WRONLY), {errno.EROFS, errno.EACCES})
    expect_denied("outside .lake truncate", lambda: os.truncate(fixture / "outside-truncate.txt", 5), {errno.EROFS, errno.EACCES})
    expect_denied("outside .lake read-only truncate-open", lambda: os.open(fixture / "outside-open-truncate.txt", os.O_RDONLY | os.O_TRUNC), {errno.EROFS, errno.EACCES})
    expect_denied("symlink from .lake to outside write", lambda: os.open(fixture / ".lake/escape-link", os.O_WRONLY), {errno.EROFS, errno.EACCES})
    expect_denied("outside .lake creation", lambda: os.open(fixture / "outside-new.txt", os.O_WRONLY | os.O_CREAT, 0o600), {errno.EROFS, errno.EACCES})

    if build:
        (fixture / ".lake/build-created.txt").write_text("permitted build fixture\n")
        print("PASS build .lake write: allowed", flush=True)
    else:
        expect_denied("export .lake write-open", lambda: os.open(fixture / ".lake/export-write.txt", os.O_WRONLY), {errno.EROFS, errno.EACCES})
        expect_denied("export .lake truncate", lambda: os.truncate(fixture / ".lake/export-truncate.txt", 5), {errno.EROFS, errno.EACCES})

    for namespace, host_value in expected_namespaces.items():
        if os.readlink(f"/proc/self/ns/{namespace}") == host_value:
            failures.append(f"{namespace}: host namespace retained")
        else:
            print(f"PASS {namespace} namespace: private", flush=True)

    if Path(f"/proc/{host_pid}").exists():
        failures.append("host parent is visible through /proc")
    else:
        print("PASS host parent: absent from private /proc", flush=True)
    expect_denied("host parent signal lookup", lambda: os.kill(host_pid, 0), {errno.ESRCH, errno.EPERM})

    network_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    network_socket.settimeout(1)
    try:
        network_socket.connect(("127.0.0.1", host_port))
        failures.append("private network reached host loopback listener")
    except OSError as error:
        print(f"PASS host loopback listener: unreachable errno={error.errno}", flush=True)
    finally:
        network_socket.close()
    expect_denied("AF_UNIX socket creation", lambda: socket.socket(socket.AF_UNIX, socket.SOCK_STREAM), {errno.EAFNOSUPPORT, errno.EPERM, errno.EACCES})

    status = dict(line.split(":", 1) for line in Path("/proc/self/status").read_text().splitlines() if ":" in line)
    if int(status["CapEff"].strip(), 16) != 0:
        failures.append("effective capabilities are not empty")
    else:
        print("PASS effective capabilities: none", flush=True)
    if status["NoNewPrivs"].strip() != "1":
        failures.append("no_new_privs is not set")
    else:
        print("PASS no_new_privs: set", flush=True)
    print(f"Sandbox UID: {os.getuid()}", flush=True)

    # Even with unrestricted program execution and a nested user namespace,
    # a child must not recover write access to an outer read-only fixture.
    escape_code = "from pathlib import Path; import sys; Path(sys.argv[1]).write_text('unexpected nested write')"
    nested = subprocess.run([
        "/usr/bin/bwrap", "--unshare-all", "--die-with-parent", "--new-session", "--cap-drop", "ALL",
        "--ro-bind", "/", "/", "--proc", "/proc", "--dev", "/dev",
        "--bind", str(fixture), str(fixture), "--", "/usr/bin/python3", "-c", escape_code,
        str(fixture / "outside-nested.txt"),
    ], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if nested.returncode == 0:
        failures.append("nested bubblewrap recovered outside write access")
    else:
        print(f"PASS nested namespace write attempt: rejected exit={nested.returncode}", flush=True)
        print(nested.stderr.strip(), flush=True)

    for failure in failures:
        print("FAIL " + failure, flush=True)
    return 1 if failures else 0


def run_probe() -> int:
    evidence = []
    failures = []
    (ROOT / ".verification-tmp").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="strict-sandbox-probe-", dir=ROOT / ".verification-tmp") as name:
        fixture = Path(name)
        (fixture / ".lake").mkdir()
        fixture_text = "disposable sandbox fixture\n"
        outer_files = ["outside-write.txt", "outside-truncate.txt", "outside-open-truncate.txt", "outside-symlink.txt", "outside-nested.txt"]
        for file_name in outer_files:
            (fixture / file_name).write_text(fixture_text)
        for file_name in ["export-write.txt", "export-truncate.txt"]:
            (fixture / ".lake" / file_name).write_text(fixture_text)
        (fixture / ".lake/escape-link").symlink_to(fixture / "outside-symlink.txt")
        namespaces = [f"{kind}={os.readlink('/proc/self/ns/' + kind)}" for kind in ["user", "pid", "mnt", "net", "ipc", "uts"]]
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(1)
            for mode in ["build", "export"]:
                landrun_args = ["--best-effort", "--ro", "/", "--rw", "/dev", "-ldd", "-add-exec", "--ro", str(fixture)]
                if mode == "build":
                    landrun_args += ["--rwx", str(fixture / ".lake")]
                command = [
                    "/usr/bin/systemd-run", "--property=RestrictAddressFamilies=~AF_UNIX", "--user", "--pty", "--wait", "--collect",
                    "--working-directory", str(fixture), "--", str(ADAPTER), *landrun_args,
                    "--", "/usr/bin/python3", str(Path(__file__).resolve()), "child", str(fixture), mode,
                    str(os.getpid()), str(listener.getsockname()[1]), *namespaces,
                ]
                result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                evidence.append(f"MODE {mode}: exit={result.returncode}\n{result.stdout}")
                if result.returncode != 0:
                    failures.append(f"{mode} probe failed")
        for file_name in outer_files:
            if (fixture / file_name).read_text() != fixture_text:
                failures.append(f"outer fixture changed: {file_name}")
        for file_name in ["export-write.txt", "export-truncate.txt"]:
            if (fixture / ".lake" / file_name).read_text() != fixture_text:
                failures.append(f"export fixture changed: {file_name}")
        if not (fixture / ".lake/build-created.txt").is_file():
            failures.append("permitted build fixture was not written")

        negative_cases = [
            ("unknown option", ["--unrestricted-filesystem"]),
            ("unexpected --rw", ["--rw", str(fixture)]),
            ("unexpected --rwx", ["--rwx", str(fixture)]),
            ("relative --rwx", ["--rwx", ".lake"]),
        ]
        for label, bad_args in negative_cases:
            command = [
                "/usr/bin/systemd-run", "--property=RestrictAddressFamilies=~AF_UNIX", "--user", "--pty", "--wait", "--collect",
                "--working-directory", str(fixture), "--", str(ADAPTER), *bad_args, "--", "/usr/bin/true",
            ]
            result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            evidence.append(f"NEGATIVE {label}: exit={result.returncode}\n{result.stdout}")
            if result.returncode != 2:
                failures.append(f"{label}: expected exit 2, received {result.returncode}")
    evidence.append("Outer and export fixture contents unchanged; only designated build fixture written." if not failures else "\n".join(failures))
    output = "\n".join(evidence)
    print(output)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(child() if len(sys.argv) > 1 and sys.argv[1] == "child" else run_probe())
