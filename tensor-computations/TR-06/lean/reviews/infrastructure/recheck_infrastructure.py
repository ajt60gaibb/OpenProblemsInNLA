#!/usr/bin/env python3
"""Retain Python-only infrastructure checks; never runs Lean or Linux Comparator."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys

DEFAULT_REPO = Path('/Users/ajt253/.codex/worktrees/tr06-formal-verification/OpenProblemsInNLA')
EXPECTED_HEAD = '0689db001ddc4c54f2652ed4b13b753637fef700'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=DEFAULT_REPO)
    parser.add_argument('--output', type=Path, default=Path('/private/tmp/tr06-infra/checks'))
    parser.add_argument('--expected-head', default=EXPECTED_HEAD)
    args = parser.parse_args()
    repo = args.repo.resolve()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    git = lambda *argv: subprocess.check_output(['git', *argv], cwd=repo, text=True).strip()
    head = git('rev-parse', 'HEAD')
    if head != args.expected_head:
        raise SystemExit(f'Expected HEAD {args.expected_head}; found {head}')
    inputs = set(repo.glob('tools/lean/*'))
    inputs.update(repo.glob('docs/lean/schema/*'))
    inputs.update(repo / p for p in [
        'tests/test_lean_verification.py', 'tests/test_problem_ids.py',
        'tools/validate_problem_ids.py', 'tools/update_catalog.py',
        'problem_ids.json', '.github/workflows/lean-verification.yml',
    ])
    hashes = {str(p.relative_to(repo)): digest(p) for p in sorted(inputs) if p.is_file()}
    commands = [
        ('project-selection-metadata', ['-m', 'unittest', 'discover', '-s', 'tests', '-p', 'test_lean_verification.py', '-v'], 30),
        ('harness-unit-tests', ['-m', 'unittest', 'discover', '-s', 'tools/lean', '-p', 'test_*.py', '-v'], 12),
        ('permanent-id-validation', ['tools/validate_problem_ids.py', '--base-ref', 'origin/main'], None),
        ('permanent-id-tests', ['-m', 'unittest', 'discover', '-s', 'tests', '-p', 'test_problem_ids.py', '-v'], 17),
    ]
    report = {
        'scope': 'Python infrastructure unit tests and permanent-ID validation only; no Lean project, LeanCert certificate, Linux sandbox controls, Comparator run, or TR-06 target verification.',
        'linux_comparator_controls_executed': False,
        'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'repository': str(repo), 'head': head, 'origin_main': git('rev-parse', 'origin/main'),
        'python_executable': sys.executable, 'python_version': sys.version,
        'platform': platform.platform(), 'script_sha256': digest(Path(__file__)),
        'input_sha256': hashes, 'checks': [],
    }
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    failed = False
    for name, arguments, expected_tests in commands:
        command = [sys.executable, *arguments]
        run = subprocess.run(command, cwd=repo, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        logfile = out / (name + '.log')
        logfile.write_text(run.stdout)
        match = re.search(r'Ran (\d+) tests? in ', run.stdout)
        tests = int(match.group(1)) if match else None
        entry = {'name': name, 'command': command, 'cwd': str(repo), 'exit_code': run.returncode,
                 'expected_tests': expected_tests, 'reported_tests': tests,
                 'log': logfile.name, 'log_sha256': digest(logfile)}
        entry['passed'] = run.returncode == 0 and (expected_tests is None or tests == expected_tests)
        failed |= not entry['passed']
        report['checks'].append(entry)
        print(f'{name}: exit={run.returncode}, tests={tests}, pass={entry["passed"]}')
    report['inputs_unchanged'] = all(digest(repo / p) == sha for p, sha in hashes.items())
    report['head_unchanged'] = git('rev-parse', 'HEAD') == head
    failed |= not report['inputs_unchanged'] or not report['head_unchanged']
    report['passed'] = not failed
    report['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    (out / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
    return int(failed)


if __name__ == '__main__':
    raise SystemExit(main())
