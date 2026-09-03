from __future__ import annotations

import os
from pathlib import Path
import sys
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "ReasBookWeb" / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from site_config import (  # noqa: E402
    load_site_config,
    parse_csv_env_set,
    parse_github_remote,
    parse_repo_slug,
    project_enabled,
)


class SiteConfigTests(unittest.TestCase):
    def test_parse_github_remote_forms(self) -> None:
        self.assertEqual(parse_github_remote("https://github.com/acme/books.git"), ("acme", "books"))
        self.assertEqual(parse_github_remote("git@github.com:acme/books"), ("acme", "books"))
        self.assertIsNone(parse_github_remote("https://gitlab.com/acme/books"))

    def test_parse_repo_slug_rejects_incomplete_values(self) -> None:
        self.assertEqual(parse_repo_slug("/acme/books/"), ("acme", "books"))
        self.assertIsNone(parse_repo_slug("acme"))
        self.assertIsNone(parse_repo_slug("acme/books/extra"))
        self.assertIsNone(parse_repo_slug("/"))

    def test_load_site_config_honors_overrides(self) -> None:
        values = {
            "REASBOOK_GITHUB_REPO": "acme/handbook",
            "REASBOOK_GITHUB_BRANCH": "release",
            "REASBOOK_SITE_BASE": "https://docs.example.test/handbook",
            "REASBOOK_SITE_ROOT": "handbook",
        }
        with patch.dict(os.environ, values, clear=True), patch(
            "site_config.detect_default_branch", return_value="main"
        ), patch("site_config._current_git_branch", return_value="dev"):
            config = load_site_config()

        self.assertEqual(config.github_owner, "acme")
        self.assertEqual(config.github_repo, "handbook")
        self.assertEqual(config.github_branch, "release")
        self.assertEqual(config.site_base, "https://docs.example.test/handbook/")
        self.assertEqual(config.site_root, "/handbook/")
        self.assertEqual(config.docs_base, "https://docs.example.test/handbook/docs/ReasBook/")

    def test_parse_csv_env_set_ignores_empty_items(self) -> None:
        with patch.dict(os.environ, {"REASBOOK_TEST_VALUES": " a, ,b ,,"}, clear=False):
            self.assertEqual(parse_csv_env_set("REASBOOK_TEST_VALUES"), {"a", "b"})

    def test_project_selection_is_explicit(self) -> None:
        with patch("site_config.INCLUDE_PROJECTS", {"books/Demo"}), patch(
            "site_config.EXCLUDE_PROJECTS", {"papers/Hidden"}
        ):
            self.assertTrue(project_enabled("books", "Demo"))
            self.assertFalse(project_enabled("books", "Other"))
            self.assertFalse(project_enabled("papers", "Hidden"))


if __name__ == "__main__":
    unittest.main()
