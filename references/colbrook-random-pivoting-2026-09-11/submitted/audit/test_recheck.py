"""Offline tests of audit safeguards; these do not fetch or clear the repository."""
from pathlib import Path
import tempfile
import unittest
from recheck_github import AuditError, Client, ROOT, match_excerpt, next_page, validate_url


class SafeguardTests(unittest.TestCase):
    def test_fixed_host_and_repository(self):
        validate_url(ROOT + "/issues?state=all")
        for url in ("http://api.github.com/repos/ajt60gaibb/OpenProblemsInNLA/issues",
                    "https://api.github.com.evil.invalid/repos/ajt60gaibb/OpenProblemsInNLA/issues",
                    "https://user:secret@api.github.com/repos/ajt60gaibb/OpenProblemsInNLA/issues",
                    ROOT + "-other/issues", "https://example.org/", ROOT.replace("api.github.com", "api.github.com:444")):
            with self.assertRaises(AuditError):
                validate_url(url)

    def test_next_link(self):
        url = ROOT + "/issues?page=2&per_page=100"
        self.assertEqual(next_page(f'<{url}>; rel="next", <{url}>; rel="last"'), url)
        self.assertIsNone(next_page(""))
        with self.assertRaises(AuditError):
            next_page('<https://example.org/>; rel="next"')

    def test_broad_target_matches(self):
        for text in ("RA-02 resolved", "RA 3 counterexample", "RPLU sharpness", "RPCholesky", "randomly pivoted LU"):
            self.assertIsNotNone(match_excerpt(text))
        self.assertIsNone(match_excerpt("Unrelated maintenance"))

    def test_pagination_collects_all_pages(self):
        with tempfile.TemporaryDirectory() as name:
            client = Client(Path(name))
            replies = [([{"number": 1}], {"link": f'<{ROOT}/issues?page=2>; rel="next"'}),
                       ([{"number": 2}], {})]
            client.get = lambda url: replies.pop(0)
            self.assertEqual([x["number"] for x in client.pages("/issues", state="all")], [1, 2])

    def test_pagination_failure_is_not_empty_search(self):
        with tempfile.TemporaryDirectory() as name:
            client = Client(Path(name))
            client.get = lambda url: ({"message": "Not a list"}, {})
            with self.assertRaises(AuditError):
                client.pages("/issues", state="all")


if __name__ == "__main__":
    unittest.main(verbosity=2)
