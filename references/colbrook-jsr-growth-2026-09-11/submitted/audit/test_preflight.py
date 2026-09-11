"""Offline preflight tests: no network requests and no repository changes."""
from __future__ import annotations
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import urllib.error
import urllib.request
from github_preflight import (
    AuditFailure, Collector, NoRedirect, canonical_destination, next_link,
)


class FakeResponse(io.BytesIO):
    def __init__(self, payload: object, *, status: int = 200,
                 headers: dict[str, str] | None = None) -> None:
        super().__init__(json.dumps(payload).encode())
        self.status = status
        self.headers = headers or {}


class PreflightTests(unittest.TestCase):
    def test_pagination(self) -> None:
        self.assertIsNone(next_link(None))
        self.assertIsNone(next_link('<https://api.github.com/x?page=1>; rel="prev"'))
        header = '<https://api.github.com/x?page=2>; rel="next", <https://api.github.com/x?page=4>; rel="last"'
        self.assertEqual(next_link(header), 'https://api.github.com/x?page=2')

    def test_repository_name_validation(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            for name in ('owner/repo/extra', '../repo', 'owner/..', 'owner/rep?x=1'):
                with self.subTest(name=name), self.assertRaises(ValueError):
                    Collector(name, Path(folder), 1, 10)

    def test_out_of_scope_url_is_never_requested(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            collector = Collector('owner/repo', Path(folder), 1, 10)
            urls = [
                'https://example.com/repos/owner/repo/issues',
                'https://api.github.com/repos/other/repo/issues',
                'https://api.github.com/repos/owner/repo/../other/issues',
                'https://api.github.com/repos/owner/repo/%2e%2e/other/issues',
                'https://api.github.com/repos/owner/repo/issues#fragment',
            ]
            with patch.object(collector.opener, 'open') as network:
                for url in urls:
                    with self.subTest(url=url), self.assertRaises(AuditFailure):
                        collector.get(url, 'bad')
                network.assert_not_called()

    def test_redirects_are_never_followed(self) -> None:
        request = urllib.request.Request(
            'https://api.github.com/repos/owner/repo/issues',
            headers={'Authorization': 'Bearer offline-test-secret'},
        )
        handler = NoRedirect()
        for code in (301, 302, 303, 307, 308):
            for newurl in ('https://example.com/steal',
                           'https://api.github.com/repos/owner/repo/issues'):
                with self.subTest(code=code, newurl=newurl), self.assertRaises(AuditFailure):
                    handler.redirect_request(request, None, code, 'Redirect', {}, newurl)

    def test_network_failure_leaves_hold(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            collector = Collector('owner/repo', Path(folder), 1, 10)
            with patch.object(collector.opener, 'open', side_effect=urllib.error.URLError('offline test')):
                result = collector.collect()
            self.assertFalse(result['transport_complete'])
            self.assertEqual(result['clearance_status'], 'NOT_CLEARED')
            self.assertTrue(result['human_review_required'])
            self.assertFalse(result['submission_performed'])
            self.assertEqual(len(result['errors']), 1)
            saved = json.loads((Path(folder) / 'preflight_report.json').read_text())
            self.assertEqual(saved['clearance_status'], 'NOT_CLEARED')

    def test_keyword_absence_is_not_clearance(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            collector = Collector('owner/repo', Path(folder), 1, 10)
            collector.documents = [('https://example.com', 'no matching title')]
            self.assertEqual(collector.keyword_matches(), [])
            self.assertFalse(hasattr(collector, 'clear_submission'))

    def test_recorded_partial_match(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            collector = Collector('owner/repo', Path(folder), 1, 10)
            collector.documents = [('https://example.com/a', 'Partial result for MF-12.')]
            self.assertEqual(collector.keyword_matches()[0]['problem'], 'MF-12')

    def test_canonical_paths_cannot_escape(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder) / 'canonical'
            for path in ('../secret', '/absolute', 'a/../../secret', 'a\\secret',
                         './a', 'a//b', 'a/./b', '', 'a\x00b'):
                with self.subTest(path=path), self.assertRaises(AuditFailure):
                    canonical_destination(root, path)
            self.assertEqual(canonical_destination(root, 'category/MF-05.md'),
                             root / 'category' / 'MF-05.md')

    def test_canonical_symlink_escape_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder) / 'canonical'
            root.mkdir()
            (root / 'out').symlink_to(Path(folder), target_is_directory=True)
            with self.assertRaises(AuditFailure):
                canonical_destination(root, 'out/secret')

    def test_http_non_200_is_incomplete(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            collector = Collector('owner/repo', Path(folder), 1, 10)
            with patch.object(collector.opener, 'open', return_value=FakeResponse({}, status=206)):
                result = collector.collect()
            self.assertFalse(result['transport_complete'])
            self.assertEqual(result['clearance_status'], 'NOT_CLEARED')

    def test_complete_transport_still_never_clears(self) -> None:
        import base64
        with tempfile.TemporaryDirectory() as folder:
            collector = Collector('owner/repo', Path(folder), 1, 100)
            branch = {'commit': {'sha': 'fake-test-commit'}}
            source = base64.b64encode(b'# MF-05 canonical test statement').decode()
            payloads = [
                branch,
                {'truncated': False, 'tree': [
                    {'path': 'matrix-functions-and-stability/MF-05.md',
                     'type': 'blob', 'sha': 'fake-test-blob'}]},
                {'encoding': 'base64', 'content': source},
                [], [], [], [], [], branch,
            ]
            with patch.object(collector.opener, 'open',
                              side_effect=[FakeResponse(p) for p in payloads]) as network:
                result = collector.collect()
            self.assertEqual(network.call_count, len(payloads))
            self.assertTrue(result['transport_complete'], result['errors'])
            self.assertEqual(result['clearance_status'], 'NOT_CLEARED')
            self.assertTrue(result['human_review_required'])
            self.assertFalse(result['submission_performed'])
            self.assertEqual(result['canonical_revision'], 'fake-test-commit')
            self.assertTrue(result['keyword_matches'])

    def test_pagination_loop_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            collector = Collector('owner/repo', Path(folder), 1, 10)
            url = 'https://api.github.com/repos/owner/repo/issues?page=1'
            response = FakeResponse([], headers={'Link': f'<{url}>; rel="next"'})
            with patch.object(collector.opener, 'open', return_value=response):
                with self.assertRaises(AuditFailure):
                    collector.pages(url, 'loop')

    def test_request_limit_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            collector = Collector('owner/repo', Path(folder), 1, 1)
            with patch.object(collector.opener, 'open', return_value=FakeResponse({})):
                collector.get('/issues', 'first')
                with self.assertRaises(AuditFailure):
                    collector.get('/issues', 'second')


if __name__ == '__main__':
    unittest.main(verbosity=2)
