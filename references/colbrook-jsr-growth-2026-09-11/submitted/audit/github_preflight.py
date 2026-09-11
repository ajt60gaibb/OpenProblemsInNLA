#!/usr/bin/env python3
"""Collect a public GitHub repository audit. This NEVER clears or submits a result.

All requests are read-only GETs. Set GITHUB_TOKEN in the environment for a larger
API allowance; the token is never written to the output. A complete API download
still requires human review of the actual arguments, linked documents, and any
attachments. Keyword absence is not evidence that a problem is untouched.

Python 3.10+, standard library only.
"""
from __future__ import annotations

import argparse
import base64
import datetime as dt
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys
from typing import Any
import urllib.error
import urllib.parse
import urllib.request

DEFAULT_REPOSITORY = "ajt60gaibb/OpenProblemsInNLA"
CATEGORY = "matrix-functions-and-stability"
TARGETS = {
    "MF-05": ["MF-05", "MF05", "local Hölder", "local Holder", "Hölder continuity", "Holder continuity"],
    "MF-07": ["MF-07", "MF07", "uniform polynomial", "trajectory bounds", "joint spectral radius one"],
    "MF-12": ["MF-12", "MF12", "polynomial growth exponent", "marginal growth", "arbitrary polynomial"],
}


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def next_link(header: str | None) -> str | None:
    """Read GitHub's RFC 8288 next-page link without guessing page counts."""
    if not header:
        return None
    for item in header.split(","):
        match = re.match(r'\s*<([^>]+)>\s*;\s*rel="([^"]+)"', item)
        if match and "next" in match.group(2).split():
            return match.group(1)
    return None


class AuditFailure(RuntimeError):
    pass


class NoRedirect(urllib.request.HTTPRedirectHandler):
    """Never follow redirects, including same-host redirects.

    An authenticated request must not silently redirect to a different host,
    repository, or URL. A moved repository must be reviewed and supplied afresh.
    """
    def redirect_request(self, req: Any, fp: Any, code: int, msg: str,
                         headers: Any, newurl: str) -> None:
        raise AuditFailure(f"Refusing HTTP redirect ({code}) during API audit")


def canonical_destination(root: Path, repository_path: str) -> Path:
    """Validate untrusted tree paths before writing a local canonical copy."""
    path = PurePosixPath(repository_path)
    if (not repository_path or "\\" in repository_path
            or path.is_absolute() or ".." in path.parts
            or "\x00" in repository_path
            or str(path) != repository_path):
        raise AuditFailure("Unsafe or noncanonical path in repository tree")
    destination = root.joinpath(*path.parts)
    # Refuse an unexpected pre-existing symlink even in an otherwise empty run.
    if not destination.resolve().is_relative_to(root.resolve()):
        raise AuditFailure("Repository path escapes canonical output directory")
    return destination


class Collector:
    def __init__(self, repository: str, output: Path, timeout: float, max_requests: int):
        if (not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository)
                or any(part in {".", ".."} for part in repository.split("/"))):
            raise ValueError("repository must have the form owner/name")
        self.repository = repository
        self.branch = "main"
        self.opener = urllib.request.build_opener(NoRedirect())
        self.root_url = f"https://api.github.com/repos/{repository}"
        self.output = output
        self.raw = output / "raw"
        self.raw.mkdir(parents=True, exist_ok=True)
        self.timeout = timeout
        self.max_requests = max_requests
        self.token = os.environ.get("GITHUB_TOKEN")
        self.requests = 0
        self.records: list[dict[str, Any]] = []
        self.errors: list[dict[str, str]] = []
        self.documents: list[tuple[str, str]] = []
        self.warnings: list[str] = []

    def get(self, path_or_url: str, label: str, *, text: bool = False) -> Any:
        url = path_or_url if path_or_url.startswith("https://") else self.root_url + path_or_url
        parsed = urllib.parse.urlparse(url)
        # Do not forward an access token to an arbitrary linked host or repository.
        decoded_path = urllib.parse.unquote(parsed.path)
        if (parsed.scheme != "https" or parsed.netloc != "api.github.com"
                or parsed.fragment or parsed.params
                or not decoded_path.startswith(f"/repos/{self.repository}/")
                or ".." in PurePosixPath(decoded_path).parts
                or "\\" in decoded_path or "\x00" in decoded_path):
            raise AuditFailure(f"Refusing out-of-scope API URL: {url}")
        if self.requests >= self.max_requests:
            raise AuditFailure(f"Request cap {self.max_requests} reached; audit incomplete")
        headers = {
            "User-Agent": "OpenProblemsInNLA-read-only-submission-preflight",
            "Accept": "application/vnd.github.diff" if text else "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
        }
        if self.token:
            headers["Authorization"] = "Bearer " + self.token
        request = urllib.request.Request(url, headers=headers, method="GET")
        self.requests += 1
        try:
            with self.opener.open(request, timeout=self.timeout) as response:
                status = response.status
                if status != 200:
                    raise AuditFailure(f"Unexpected HTTP {status} at {url}")
                payload = response.read()
                response_headers = dict(response.headers.items())
        except urllib.error.HTTPError as exc:
            reset = exc.headers.get("X-RateLimit-Reset", "unknown")
            raise AuditFailure(f"HTTP {exc.code} at {url}; rate-limit reset epoch {reset}") from exc
        except (urllib.error.URLError, TimeoutError, OSError) as exc:
            raise AuditFailure(f"GET failed at {url}: {exc}") from exc
        safe_label = re.sub(r"[^A-Za-z0-9_.-]", "_", label)
        destination = self.raw / (safe_label + (".diff" if text else ".json"))
        destination.write_bytes(payload)
        record = {
            "url": url, "status": status, "file": str(destination.relative_to(self.output)),
            "sha256": hashlib.sha256(payload).hexdigest(), "bytes": len(payload),
            "retrieved_utc": utc_now(),
            "next": next_link(response_headers.get("Link") or response_headers.get("link")),
        }
        self.records.append(record)
        try:
            decoded = payload.decode("utf-8")
        except UnicodeError as exc:
            raise AuditFailure(f"Invalid UTF-8 at {url}") from exc
        self.documents.append((url, decoded))
        if text:
            return decoded
        try:
            return json.loads(decoded)
        except (UnicodeError, json.JSONDecodeError) as exc:
            raise AuditFailure(f"Invalid JSON at {url}") from exc

    def pages(self, path: str, label: str) -> list[dict[str, Any]]:
        answer: list[dict[str, Any]] = []
        url: str | None = path
        page = 1
        seen: set[str] = set()
        while url:
            if url in seen:
                raise AuditFailure(f"Pagination loop in {label}")
            seen.add(url)
            batch = self.get(url, f"{label}_{page:04d}")
            if not isinstance(batch, list):
                raise AuditFailure(f"Expected a JSON array for {label}, page {page}")
            answer.extend(batch)
            url = self.records[-1]["next"]
            page += 1
        return answer

    def collect(self) -> dict[str, Any]:
        result: dict[str, Any] = {
            "repository": self.repository,
            "started_utc": utc_now(),
            "clearance_status": "NOT_CLEARED",
            "transport_complete": False,
            "human_review_required": True,
            "submission_performed": False,
        }
        try:
            # The user-supplied category URL targets main. Pin its current commit,
            # or the branch explicitly supplied with --branch, for comparison.
            branch = self.get("/branches/" + urllib.parse.quote(self.branch, safe=""), "branch_start")
            revision = branch["commit"]["sha"]
            result["canonical_revision"] = revision
            tree = self.get(f"/git/trees/{revision}?recursive=1", "tree")
            if tree.get("truncated"):
                raise AuditFailure("Git tree is truncated; canonical-source audit incomplete")
            paths: list[str] = []
            for item in tree.get("tree", []):
                path = item["path"]
                is_category_text = path.startswith(CATEGORY + "/") and path.lower().endswith((".md", ".txt", ".tex", ".rst"))
                is_policy = path.upper() in {"README.MD", "RESOLVED.MD", "CONTRIBUTING.MD", "SUBMISSION.MD", "LICENSE"}
                is_template = path.startswith(".github/") and path.lower().endswith((".md", ".yml", ".yaml"))
                if item.get("type") == "blob" and (is_category_text or is_policy or is_template):
                    blob = self.get(f"/git/blobs/{item['sha']}", f"blob_{item['sha']}")
                    if blob.get("encoding") != "base64":
                        raise AuditFailure(f"Unsupported blob encoding for {path}")
                    content = base64.b64decode(blob["content"], validate=False).decode("utf-8")
                    local = canonical_destination(self.output / "canonical", path)
                    local.parent.mkdir(parents=True, exist_ok=True)
                    local.write_text(content, encoding="utf-8")
                    self.documents.append((f"https://github.com/{self.repository}/blob/{revision}/{path}", content))
                    paths.append(path)
            result["canonical_files"] = paths
            if not any(path.startswith(CATEGORY + "/") for path in paths):
                raise AuditFailure("No canonical category text files were retrieved")

            issues = self.pages("/issues?state=all&per_page=100&sort=created&direction=asc", "issues")
            comments = self.pages("/issues/comments?per_page=100&sort=created&direction=asc", "issue_comments")
            pulls = self.pages("/pulls?state=all&per_page=100&sort=created&direction=asc", "pull_requests")
            review_comments = self.pages("/pulls/comments?per_page=100&sort=created&direction=asc", "pull_review_comments")
            issue_prs = {row["number"] for row in issues if "pull_request" in row}
            if issue_prs != {row["number"] for row in pulls}:
                raise AuditFailure("Issue-list/PR-list mismatch; repository may have changed during collection")
            result["counts"] = {
                "issues_including_pull_requests": len(issues), "pull_requests": len(pulls),
                "issue_and_pr_comments": len(comments), "pull_review_comments": len(review_comments),
            }
            for issue in issues:
                number = issue["number"]
                self.pages(f"/issues/{number}/timeline?per_page=100", f"timeline_{number}")
            review_count = 0
            for pull in pulls:
                number = pull["number"]
                detail = self.get(f"/pulls/{number}", f"pull_detail_{number}")
                reviews = self.pages(f"/pulls/{number}/reviews?per_page=100", f"pull_reviews_{number}")
                review_count += len(reviews)
                files = self.pages(f"/pulls/{number}/files?per_page=100", f"pull_files_{number}")
                if len(files) != detail.get("changed_files"):
                    raise AuditFailure(f"PR {number}: changed-file count mismatch or API truncation")
                self.get(f"/pulls/{number}", f"pull_diff_{number}", text=True)
                for file in files:
                    if "patch" not in file and file.get("changes", 0):
                        self.warnings.append(f"PR {number}: {file['filename']} has no text patch; inspect full content manually")
            result["counts"]["pull_reviews"] = review_count

            # Fail closed if the issue/PR bodies changed during the collection.
            issues_after = self.pages("/issues?state=all&per_page=100&sort=created&direction=asc", "issues_recheck")
            before = {(item["number"], item.get("updated_at")) for item in issues}
            after = {(item["number"], item.get("updated_at")) for item in issues_after}
            if before != after:
                raise AuditFailure("Issue/PR metadata changed during collection; repeat and reconcile snapshots")
            branch_after = self.get("/branches/" + urllib.parse.quote(self.branch, safe=""), "branch_end")
            if branch_after["commit"]["sha"] != revision:
                raise AuditFailure("Default target branch changed during collection; repeat canonical comparison")
            result["transport_complete"] = True
        except (AuditFailure, KeyError, ValueError, TypeError, UnicodeError) as exc:
            self.errors.append({"time_utc": utc_now(), "error": str(exc)})
        finally:
            result.update({
                "completed_utc": utc_now(), "request_count": self.requests,
                "errors": self.errors, "warnings": self.warnings,
                "records": self.records,
                "keyword_matches": self.keyword_matches(),
                "external_links": self.external_links(),
                "required_review": [
                    "Read every open and closed issue, PR, discussion/review body, comment, and relevant changed file; do not rely only on keyword matches.",
                    "Inspect linked solutions and attachments. API diff completeness does not imply an attached PDF was read.",
                    "Compare each exact canonical problem statement, including every quantifier and excluded case, against the proposed theorem.",
                    "Exclude a target if any prior issue or PR lists a solution; retain the source URL and rationale. This package conservatively also excludes recorded partial solutions.",
                    "Recheck immediately before submission because a snapshot can become stale.",
                ],
            })
            (self.output / "preflight_report.json").write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
        return result

    def keyword_matches(self) -> list[dict[str, Any]]:
        result = []
        for url, content in self.documents:
            folded = content.casefold()
            for problem, terms in TARGETS.items():
                matches = [term for term in terms if term.casefold() in folded]
                if matches:
                    result.append({"problem": problem, "url": url, "matched_terms": matches})
        return result

    def external_links(self) -> list[str]:
        urls: set[str] = set()
        for _, content in self.documents:
            for url in re.findall(r"https?://[^\s<>\"\\]+", content):
                urls.add(url.rstrip(").,;]"))
        return sorted(urls)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--repository", default=DEFAULT_REPOSITORY)
    parser.add_argument("--branch", default="main", help="target branch from the submission request; verify against repository policy")
    parser.add_argument("--output", type=Path, default=Path("github_preflight_output"))
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument("--max-requests", type=int, default=10000)
    args = parser.parse_args()
    if args.timeout <= 0 or args.max_requests < 1:
        parser.error("timeout and max-requests must be positive")
    if args.output.exists() and any(args.output.iterdir()):
        parser.error("output directory must be empty or absent; keep snapshots separate")
    collector = Collector(args.repository, args.output, args.timeout, args.max_requests)
    collector.branch = args.branch
    report = collector.collect()
    print(json.dumps({key: report[key] for key in ("clearance_status", "transport_complete", "human_review_required", "request_count", "errors")}, indent=2))
    print(f"Report: {args.output / 'preflight_report.json'}")
    print("No remote changes were made. Clearance remains NOT_CLEARED even if every GET succeeded.")
    return 0 if report["transport_complete"] else 2


if __name__ == "__main__":
    sys.exit(main())
