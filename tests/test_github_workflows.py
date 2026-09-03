from __future__ import annotations

from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS = ROOT / ".github" / "workflows"


class GitHubWorkflowPolicyTests(unittest.TestCase):
    def test_release_pages_has_one_derived_input_and_scoped_permissions(self) -> None:
        text = (WORKFLOWS / "publish_release_pages.yml").read_text(encoding="utf-8")

        self.assertIn("release_tag:", text)
        self.assertIn("workflow_dispatch:", text)
        self.assertNotIn("  push:", text)
        self.assertNotIn("bundle_asset:", text)
        self.assertNotIn("bundle_sha256:", text)
        self.assertIn("permissions: {}", text)
        self.assertIn("pages: read", text)
        self.assertIn("pages: write", text)
        self.assertIn("id-token: write", text)
        self.assertIn("github-pages-production", text)
        self.assertIn("git/ref/tags/$RELEASE_TAG", text)
        self.assertIn('"$GITHUB_REF_TYPE" == branch', text)
        self.assertIn('"$GITHUB_REF_NAME" == "$default_branch"', text)
        self.assertIn("compare/$object_sha...$GITHUB_SHA", text)
        self.assertIn('"$comparison" == ahead', text)
        self.assertIn("release-manifest.json", text)
        self.assertIn("release-set.json", text)
        self.assertIn(".pages.site.tar.zst", text)
        self.assertIn('manifest.get("artifact") != "pages"', text)
        self.assertIn('manifest.get("base_path") != "/ReasBook/"', text)
        self.assertIn("850_000_000", text)
        self.assertIn("SHA256SUMS", text)
        self.assertIn("cmp .release/release-manifest.json", text)
        self.assertIn("actions/configure-pages@", text)
        self.assertIn("persist-credentials: false", text)
        self.assertNotIn("lake build", text)
        self.assertNotIn("lake exe", text)

        actions = re.findall(r"uses:\s*([^@\s]+)@([^\s#]+)", text)
        self.assertEqual(len(actions), 5)
        for action, revision in actions:
            with self.subTest(action=action):
                self.assertRegex(revision, r"^[0-9a-f]{40}$")

    def test_superseded_github_builders_are_removed(self) -> None:
        for name in ("deploy_pages.yml", "deploy_preview.yml", "docs_full.yml"):
            self.assertFalse((WORKFLOWS / name).exists(), name)


if __name__ == "__main__":
    unittest.main()
