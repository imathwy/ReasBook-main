"""Release selection must not mix unrelated books or unverified source versions."""

import json
import hashlib
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from artifacts import EvidenceResolver


class ReleaseIdentityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.releases = self.root / "releases"
        self.data = self.root / "data"
        self.book = {
            "slug": "sample_book", "kind": "book",
            "projectPath": "ReasBook/Books/Sample_Book", "branches": ["v4.30.0"],
        }
        self.environment = patch.dict(os.environ, {"REASBOOK_REVIEWER_RELEASE_ROOT": str(self.releases)})
        self.environment.start()
        self.addCleanup(self.environment.stop)

    def write(self, path: Path, value: dict | str) -> Path:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value) if isinstance(value, dict) else value, encoding="utf-8")
        return path

    def resolver(self) -> EvidenceResolver:
        return EvidenceResolver(self.book, project_root=self.root, data_root=self.data)

    def release(self, name: str, *, project: str = "Sample_Book", commit: str = "same-commit") -> Path:
        release = self.releases / name
        digest = "sha256:" + hashlib.sha256(name.encode("utf-8")).hexdigest()
        self.write(release / "release-spec.json", {"projects": [{
            "project_id": project, "slug": project.lower(), "kind": "books",
            "branch": "v4.30.0", "commit": commit,
        }], "branches": [{"name": "v4.30.0", "commit": commit}],
            "release_id": name, "spec_digest": digest})
        site = release / "branches/v4.30.0/site"
        (site / "docs/ReasBook").mkdir(parents=True)
        self.write(release / "branches/v4.30.0/result.json", {
            "schema_version": 1, "status": "success", "error": None,
            "release_id": name, "spec_digest": digest, "branch": "v4.30.0",
            "commit": commit, "site_root": str(site.resolve()),
        })
        return release

    def source(self, release: Path) -> Path:
        return self.write(release / "worktrees/v4.30.0/ReasBook/Books/Sample_Book/Book.lean", "theorem sample : True := by trivial\n").parent

    def test_newer_unrelated_docs_do_not_hide_book_release(self) -> None:
        older = self.release("older")
        newer = self.release("newer", project="Unrelated_Book")
        os.utime(older, (1, 1))
        os.utime(newer, (2, 2))
        self.assertEqual(self.resolver().resolve().release_id, "older")

    def test_legacy_project_docs_are_rejected_without_release_spec(self) -> None:
        release = self.releases / "legacy"
        self.write(release / "branches/v4.30.0/site/docs/ReasBook/Sample_Book/Book.html", "docs")
        self.assertIsNone(self.resolver().resolve())

    def test_docs_support_book_and_paper_module_prefixes(self) -> None:
        for kind in ("book", "paper"):
            with self.subTest(kind=kind):
                self.book["kind"] = kind
                self.book["projectPath"] = f"ReasBook/{kind.title()}s/Sample_Book"
                release = self.release(f"docs-{kind}")
                target = self.write(
                    release / f"branches/v4.30.0/site/docs/ReasBook/{kind.title()}s/Sample_Book/Chap01/Example.html",
                    "<html>module documentation</html>",
                )
                resolver = self.resolver()
                self.assertEqual(resolver.docs_path("Chap01/Example.lean"), target)
                url = resolver.manifest("/api/books/sample_book", {"sourcePath": "Chap01/Example.lean"})["docs"]["url"]
                self.assertTrue(url.endswith(f"/{kind.title()}s/Sample_Book/Chap01/Example.html"))

    def test_verso_exact_module_pages_use_project_collection(self) -> None:
        for kind in ("book", "paper"):
            with self.subTest(kind=kind):
                self.book["kind"] = kind
                self.book["projectPath"] = f"ReasBook/{kind.title()}s/Sample_Book"
                release = self.release(f"verso-{kind}")
                root = release / f"branches/v4.30.0/site/{kind}s/sample_book"
                target = self.write(root / "chap01/example/index.html", "<html>module</html>")
                landing = self.write(root / "index.html", "<html>project home</html>")
                self.write(root / "chap01/index.html", "<html>chapter index</html>")
                resolver = self.resolver()
                self.assertEqual(resolver.verso_path("Chap01/Example.lean"), target)
                self.assertEqual(resolver.verso_path("Book.lean"), landing)
                self.assertIsNone(resolver.verso_path("Chap01/Missing.lean"))
                self.assertIsNone(resolver.verso_path("../Sample_Book/Book.lean"))

    def test_curated_map_reads_literal_and_preserves_original_renderer_route(self) -> None:
        release = self.release("curated")
        root = release / "branches/v4.30.0/site/theorem-maps/books/sample_book"
        metadata = {
            "schemaVersion": 1, "nodes": 2, "edges": 1,
            "generation": {"mode": "curated-static"},
            "project": {"id": "Sample_Book", "kind": "books", "branch": "v4.30.0", "commit": "same-commit"},
        }
        self.write(root / "metadata.json", metadata)
        original = self.write(root / "app.js", 'var ITEMS = [{id: "base", dependencies: []}, {id: "result", dependencies: ["base"]}];')
        self.write(root / "index.html", "<html>Original curated map</html>")
        resolver = self.resolver()
        payload = resolver.graph_payload()
        self.assertEqual(payload["generation"]["mode"], "curated-static")
        self.assertEqual(payload["items"][1]["dependencies"], ["base"])
        self.assertNotIn("proofDependencies", payload["items"][1])
        self.assertEqual(payload["items"][1]["dependencyEvidence"], "curated")
        self.assertTrue(resolver.resolve().graph_available)
        self.assertEqual(resolver.evidence_file("graph", "original/app.js")[0], original)
        self.assertNotEqual(resolver.evidence_file("graph", "app.js")[0], original)
        self.assertTrue(resolver.manifest("/api/books/sample_book", {})["graph"]["url"].endswith("graph/index.html"))

        for script in (
            'var ITEMS = [{id: "base", dependencies: runCode()}];',
            'var ITEMS = [{id: "base", dependencies: []}, {id: "result", dependencies: ["unknown"]}];',
            'var ITEMS = [{id: "base", dependencies: []}];',
        ):
            with self.subTest(script=script):
                self.write(original, script)
                self.assertIsNone(self.resolver().graph_payload())
        self.write(original, 'var ITEMS = [{id: "base", dependencies: []}, {id: "result", dependencies: ["base"]}];')
        metadata["project"]["commit"] = "stale-commit"
        self.write(root / "metadata.json", metadata)
        self.assertIsNone(self.resolver().graph_payload())

    def test_borrowed_source_requires_known_matching_identity(self) -> None:
        current = self.release("current")
        older = self.releases / "source-only"
        source = self.source(older)
        self.assertIsNone(self.resolver().resolve().source_root)
        marker = older / "worktrees/v4.30.0/.reasbook-release-source.json"
        self.write(marker, {"commit": "different-commit"})
        self.assertIsNone(self.resolver().resolve().source_root)
        self.write(marker, {"commit": "same-commit"})
        evidence = self.resolver().resolve()
        self.assertEqual(evidence.release_id, current.name)
        self.assertEqual(evidence.source_root, source)

    def test_borrowed_source_accepts_matching_release_spec_without_marker(self) -> None:
        older = self.release("older")
        source = self.source(older)
        current = self.release("current")
        os.utime(older, (1, 1))
        os.utime(current, (2, 2))
        evidence = self.resolver().resolve()
        self.assertEqual(evidence.release_id, current.name)
        self.assertEqual(evidence.source_root, source)

    def test_matching_partial_graph_can_supply_branch_release_membership(self) -> None:
        release = self.release("branch-release", project="Unrelated_Book")
        self.write(self.data / "books/sample_book/index.json", {"branch": "v4.30.0", "commit": "same-commit"})
        graph = self.data / "books/sample_book/theorem-map"
        self.write(graph / "index.html", "graph")
        self.write(graph / "data.json", {
            "schemaVersion": 2,
            "project": {"id": "Sample_Book", "kind": "books", "branch": "v4.30.0", "commit": "same-commit"},
            "generation": {"mode": "lean-environment-partial", "dependencyModel": "statement-and-proof-v1", "dependencyCoverage": "partial"},
            "items": [{"id": "sample", "dependencies": []}],
        })
        spec_path = release / "release-spec.json"
        spec = json.loads(spec_path.read_text())
        for membership in ("other-project", "missing-projects"):
            with self.subTest(membership=membership):
                if membership == "missing-projects":
                    spec.pop("projects")
                    self.write(spec_path, spec)
                evidence = self.resolver().resolve()
                self.assertIsNotNone(evidence)
                self.assertEqual(evidence.release_id, release.name)
                self.assertEqual(evidence.graph_path, graph / "data.json")
        # Keep the branch result internally valid while moving to another
        # commit. The old typed overlay must no longer establish membership.
        spec["branches"][0]["commit"] = "different-commit"
        self.write(spec_path, spec)
        result_path = release / "branches/v4.30.0/result.json"
        result = json.loads(result_path.read_text())
        result["commit"] = "different-commit"
        self.write(result_path, result)
        self.assertIsNone(self.resolver().resolve())

    def test_failed_branch_result_is_not_evidence(self) -> None:
        release = self.release("failed")
        result = json.loads((release / "branches/v4.30.0/result.json").read_text())
        result["status"] = "failed"
        (release / "branches/v4.30.0/result.json").write_text(json.dumps(result))
        self.assertIsNone(self.resolver().resolve())

    def test_digest_mismatch_is_not_evidence(self) -> None:
        release = self.release("mismatched-digest")
        result_path = release / "branches/v4.30.0/result.json"
        result = json.loads(result_path.read_text())
        result["spec_digest"] = "sha256:" + "0" * 64
        result_path.write_text(json.dumps(result))
        self.assertIsNone(self.resolver().resolve())

    def test_site_root_mismatch_is_not_evidence(self) -> None:
        release = self.release("mismatched-site")
        result_path = release / "branches/v4.30.0/result.json"
        result = json.loads(result_path.read_text())
        result["site_root"] = str(self.root / "elsewhere")
        result_path.write_text(json.dumps(result))
        self.assertIsNone(self.resolver().resolve())


if __name__ == "__main__":
    unittest.main()
