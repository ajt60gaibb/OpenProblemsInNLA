#!/usr/bin/env python3
"""Collect a read-only GitHub exclusion audit; NEVER certify eligibility automatically.

Only HTTPS GET requests to this repository on api.github.com are permitted.
All issue states, issue/PR conversation comments, PR review comments, review
bodies, and changed-file records are collected with pagination. Linked PDFs,
images, and external attachments still require human inspection.

Usage:
    python recheck_github.py --out fresh_audit
Optional environment variable: GITHUB_TOKEN (read-only access is sufficient).
The script does not post, edit, close, label, or otherwise change anything on GitHub.
"""
from __future__ import annotations

import argparse
import base64
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import sys
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.parse import quote, urlencode, urlsplit
from urllib.request import HTTPRedirectHandler, Request, build_opener

REPOSITORY = "ajt60gaibb/OpenProblemsInNLA"
ROOT = f"https://api.github.com/repos/{REPOSITORY}"
API_VERSION = "2026-03-10"
PATTERN = re.compile(
    r"\bRA[-_\s]*0?[23]\b|RPCholesky|RPLU|randomly\s+pivoted\s+(?:Cholesky|LU)|"
    r"error[-\s]+doubling|polynomial.{0,100}Cholesky|sharp.{0,100}pivot", re.I | re.S)
SOLUTION_WORDS = re.compile(r"solv(?:e|ed|es|ing)|solution|resolution|counterexample|disprov|refut|sharp", re.I)
CONTENT_PATHS = (
    "README.md", "RESOLVED.md", "randomized-and-low-rank-approximation/README.md",
    "randomized-and-low-rank-approximation/RA-02/problem.tex",
    "randomized-and-low-rank-approximation/RA-03/problem.tex",
)


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


class AuditError(RuntimeError):
    """A collection gap; it must never be interpreted as an empty search."""


def validate_url(url: str) -> None:
    parsed = urlsplit(url)
    expected_path = f"/repos/{REPOSITORY}"
    if (parsed.scheme != "https" or parsed.hostname != "api.github.com"
            or parsed.port not in (None, 443) or parsed.username or parsed.password
            or not (parsed.path == expected_path or parsed.path.startswith(expected_path + "/"))):
        raise AuditError("Refused an API URL outside the fixed public repository")


class NoRedirects(HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        # In particular, do not forward an Authorization header to a redirect.
        raise AuditError("API redirect refused; review the repository address manually")


def next_page(link: str) -> str | None:
    for entry in link.split(","):
        match = re.match(r'\s*<([^>]+)>\s*;\s*rel="([^"]+)"', entry)
        if match and match.group(2) == "next":
            validate_url(match.group(1))
            return match.group(1)
    if re.search(r'rel\s*=\s*["\']?next', link, re.I):
        raise AuditError("Could not parse a next-page link; collection is incomplete")
    return None


def match_excerpt(text: str) -> str | None:
    match = PATTERN.search(text)
    if match is None:
        return None
    return text[max(0, match.start() - 180):min(len(text), match.end() + 500)]


class Client:
    def __init__(self, out: Path, timeout: float = 20.0, max_requests: int = 1000):
        self.out, self.timeout, self.max_requests = out, timeout, max_requests
        self.calls = 0
        self.requests: list[dict[str, Any]] = []
        self.matches: list[dict[str, Any]] = []
        self.notes: list[str] = []
        self.token = os.environ.get("GITHUB_TOKEN", "")
        self.opener = build_opener(NoRedirects())
        (out / "raw").mkdir(parents=True, exist_ok=True)

    def get(self, url: str) -> tuple[Any, dict[str, str]]:
        validate_url(url)
        if self.calls >= self.max_requests:
            raise AuditError("Request limit reached; collection is incomplete")
        self.calls += 1
        headers = {"Accept": "application/vnd.github+json",
                   "X-GitHub-Api-Version": API_VERSION,
                   "User-Agent": "NLA-read-only-exclusion-audit"}
        if self.token:
            headers["Authorization"] = "Bearer " + self.token
        request = Request(url, headers=headers, method="GET")
        try:
            with self.opener.open(request, timeout=self.timeout) as response:
                body = response.read(32 * 1024 * 1024 + 1)
                response_headers = dict(response.headers.items())
                status = response.status
        except HTTPError as error:
            # Do not echo arbitrary server bodies or request headers/tokens.
            raise AuditError(f"GitHub returned HTTP {error.code}; URL: {url}") from None
        except (URLError, TimeoutError, OSError) as error:
            raise AuditError(f"Network read failed ({type(error).__name__}); URL: {url}") from None
        if len(body) > 32 * 1024 * 1024:
            raise AuditError("An API response exceeded the 32 MiB safety limit")
        try:
            data = json.loads(body)
        except (ValueError, UnicodeError):
            raise AuditError("An API response was not valid JSON") from None
        filename = f"raw/{self.calls:05d}.json"
        (self.out / filename).write_bytes(body)
        lower_headers = {k.lower(): v for k, v in response_headers.items()}
        self.requests.append({"url": url, "status": status, "saved_as": filename,
                              "sha256": hashlib.sha256(body).hexdigest(),
                              "github_date": lower_headers.get("date"),
                              "request_id": lower_headers.get("x-github-request-id"),
                              "rate_limit_remaining": lower_headers.get("x-ratelimit-remaining")})
        return data, lower_headers

    def pages(self, endpoint: str, **params: Any) -> list[dict[str, Any]]:
        params["per_page"] = 100
        url: str | None = ROOT + endpoint + "?" + urlencode(params)
        result: list[dict[str, Any]] = []
        seen: set[str] = set()
        while url:
            if url in seen:
                raise AuditError("Repeated pagination URL; collection is incomplete")
            seen.add(url)
            data, headers = self.get(url)
            if not isinstance(data, list) or any(not isinstance(x, dict) for x in data):
                raise AuditError("Expected a list of API objects while paginating")
            result.extend(data)
            url = next_page(headers.get("link", ""))
        return result

    def scan(self, record: dict[str, Any], kind: str, fallback_url: str = "") -> None:
        fields = [record.get(key, "") or "" for key in ("title", "body", "filename", "patch")]
        text = "\n".join(str(x) for x in fields)
        excerpt = match_excerpt(text)
        if excerpt is not None:
            self.matches.append({"kind": kind, "number": record.get("number"),
                                 "url": record.get("html_url") or fallback_url,
                                 "title": record.get("title"), "excerpt": excerpt,
                                 "solution_word_also_present": bool(SOLUTION_WORDS.search(text))})

    def content(self, path: str, commit: str) -> dict[str, Any]:
        data, _ = self.get(ROOT + "/contents/" + quote(path, safe="/") + "?" + urlencode({"ref": commit}))
        if not isinstance(data, dict) or data.get("type") != "file" or data.get("encoding") != "base64":
            raise AuditError(f"Expected an inline base64 source file: {path}")
        try:
            raw = base64.b64decode("".join(data["content"].split()), validate=True)
            text = raw.decode("utf-8")
        except (ValueError, KeyError, UnicodeError):
            raise AuditError(f"Could not decode source file: {path}") from None
        local_name = f"source_{len(self.requests):05d}.txt"
        (self.out / local_name).write_text(text, encoding="utf-8")
        self.scan({"title": path, "body": text, "html_url": data.get("html_url")}, "source-file")
        return {"path": path, "commit": commit, "blob_sha": data.get("sha"),
                "saved_as": local_name, "sha256": hashlib.sha256(raw).hexdigest()}


def collect(client: Client) -> dict[str, Any]:
    issues = client.pages("/issues", state="all", sort="created", direction="asc")
    for item in issues:
        client.scan(item, "pull-request" if "pull_request" in item else "issue")
    conversations = client.pages("/issues/comments", sort="created", direction="asc")
    for item in conversations:
        client.scan(item, "issue-or-PR-conversation-comment")
    review_comments = client.pages("/pulls/comments", sort="created", direction="asc")
    for item in review_comments:
        client.scan(item, "PR-review-comment")
    pulls = [item for item in issues if "pull_request" in item]
    file_count = review_count = 0
    for item in pulls:
        number = int(item["number"])
        details, _ = client.get(ROOT + f"/pulls/{number}")
        if not isinstance(details, dict):
            raise AuditError(f"PR #{number}: expected a detail object")
        client.scan(details, "PR-details")
        files = client.pages(f"/pulls/{number}/files")
        expected = details.get("changed_files")
        if not isinstance(expected, int) or expected > 3000 or len(files) != expected:
            raise AuditError(f"PR #{number}: changed-file coverage is incomplete (API maximum 3000)")
        for file in files:
            client.scan(file, "PR-changed-file", item.get("html_url", ""))
            if not file.get("patch"):
                client.notes.append(f"PR #{number}: no text patch for {file.get('filename')}; inspect manually")
        file_count += len(files)
        reviews = client.pages(f"/pulls/{number}/reviews")
        for review in reviews:
            client.scan(review, "PR-review-body", item.get("html_url", ""))
        review_count += len(reviews)
    commit, _ = client.get(ROOT + "/commits/main")
    sha = commit.get("sha") if isinstance(commit, dict) else None
    if not isinstance(sha, str) or not re.fullmatch(r"[0-9a-fA-F]{40}", sha):
        raise AuditError("Could not pin current main-branch source files to a commit")
    sources = [client.content(path, sha) for path in CONTENT_PATHS]
    return {"issues_and_PRs": len(issues), "PRs": len(pulls),
            "conversation_comments": len(conversations), "review_comments": len(review_comments),
            "review_bodies": review_count, "changed_file_records": file_count,
            "pinned_source_commit": sha, "sources": sources}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="New output directory; existing report is not overwritten")
    parser.add_argument("--timeout", type=float, default=20.0)
    parser.add_argument("--max-requests", type=int, default=1000)
    args = parser.parse_args()
    if args.timeout <= 0 or args.max_requests < 1:
        parser.error("timeout and max-requests must be positive")
    if (args.out / "report.json").exists():
        parser.error("This directory already contains report.json; choose a fresh directory")
    args.out.mkdir(parents=True, exist_ok=True)
    started = utc_now()
    client = Client(args.out, args.timeout, args.max_requests)
    complete = False
    counts: dict[str, Any] = {}
    error: str | None = None
    try:
        counts = collect(client)
        complete = True
    except (AuditError, ValueError, KeyError, TypeError) as caught:
        error = str(caught)
    report = {"repository": REPOSITORY, "started_utc": started, "finished_utc": utc_now(),
              "status": "FETCHED_REQUIRES_HUMAN_REVIEW" if complete else "INCOMPLETE",
              "eligible_for_submission": None,
              "important": "This script NEVER determines eligibility. Read all records, linked solutions, and the current statements.",
              "error": error, "api_version": API_VERSION, "request_count": client.calls,
              "counts": counts, "matches": client.matches, "requests": client.requests,
              "manual_review_notes": client.notes + [
                  "Keyword matches are a navigation aid, not a complete semantic search.",
                  "Inspect linked files, attachments, images, edited/deleted material, and unnamed omnibus resolutions manually.",
                  "Issues/comments can change during collection; recheck immediately before any submission.",
                  "Read the exact RA-02 and RA-03 statements and repository contribution rules."]}
    (args.out / "report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(report["status"])
    if error:
        print(error, file=sys.stderr)
    print(f"Saved {args.out / 'report.json'}; no GitHub changes were made.")
    return 0 if complete else 2


if __name__ == "__main__":
    raise SystemExit(main())
