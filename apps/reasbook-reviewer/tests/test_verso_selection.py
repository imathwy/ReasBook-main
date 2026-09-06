import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from verso_selection import selected_verso


class VersoSelectionTests(unittest.TestCase):
    def test_selection_is_explicit_pinned_and_source_bound(self):
        with tempfile.TemporaryDirectory() as temp:
            data = Path(temp)
            releases = data / "releases"
            release = releases / "approved"
            root = release / "project-finalizers/v4.30.0/books_Sample"
            site = root / "site"
            (site / "sample").mkdir(parents=True)
            spec = {"release_id": "approved", "spec_digest": "sha256:test", "projects": [
                {"project_id": "Sample", "kind": "books", "branch": "v4.30.0", "commit": "abc"}]}
            (release / "release-spec.json").write_text(json.dumps(spec))
            result = {"schema_version": 1, "release_id": "approved", "spec_digest": "sha256:test",
                      "project_key": "books/Sample", "branch": "v4.30.0", "commit": "abc",
                      "site_root": str(site), "status": "success", "error": None,
                      "stages": [{"name": name, "status": status} for name, status in
                                 [("lean", "skipped"), ("preflight", "success"),
                                  ("verso", "success"), ("stage-site", "success")]]}
            result_path = root / "result.json"
            result_path.write_text(json.dumps(result))
            kwargs = dict(slug="sample", project_key="books/Sample", branch="v4.30.0", commit="abc")
            self.assertIsNone(selected_verso(data, releases, **kwargs))
            manifest = {"schemaVersion": 1, "books": {"sample": {
                "releaseId": "approved", "resultSha256": hashlib.sha256(result_path.read_bytes()).hexdigest()}}}
            selection = data / "verso-selections.json"
            selection.write_text(json.dumps(manifest))
            self.assertEqual(selected_verso(data, releases, **kwargs), (site, "approved"))
            self.assertIsNone(selected_verso(data, releases, **{**kwargs, "commit": "other"}))
            self.assertIsNone(selected_verso(data, releases, **{**kwargs, "project_key": "books/Other"}))
            result["status"] = "failed"
            result_path.write_text(json.dumps(result))
            self.assertIsNone(selected_verso(data, releases, **kwargs))
            manifest["books"]["sample"]["resultSha256"] = hashlib.sha256(result_path.read_bytes()).hexdigest()
            selection.write_text(json.dumps(manifest))
            self.assertIsNone(selected_verso(data, releases, **kwargs))
            manifest["books"]["sample"]["releaseId"] = "../approved"
            selection.write_text(json.dumps(manifest))
            self.assertIsNone(selected_verso(data, releases, **kwargs))
