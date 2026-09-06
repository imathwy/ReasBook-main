from __future__ import annotations

import json
import hashlib
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from artifacts import (
    EvidenceResolver,
    _declaration_assignment,
    GRAPH_ASSETS,
    rewrite_html_for_proxy,
)


def _mark_release_success(release: Path, *, branch: str, commit: str, project_id: str = "Sample_Book") -> None:
    """Attach the immutable release identity required by EvidenceResolver."""

    digest = "sha256:" + hashlib.sha256(release.name.encode("utf-8")).hexdigest()
    spec_path = release / "release-spec.json"
    spec = json.loads(spec_path.read_text(encoding="utf-8"))
    spec.update({"release_id": release.name, "spec_digest": digest})
    spec.setdefault("branches", [{"name": branch, "commit": commit}])
    spec["projects"] = [dict(entry, branch=entry.get("branch", branch), commit=entry.get("commit", commit)) for entry in spec.get("projects", [])]
    spec_path.write_text(json.dumps(spec), encoding="utf-8")
    site = release / "branches" / branch / "site"
    (release / "branches" / branch / "result.json").write_text(
        json.dumps({
            "schema_version": 1, "status": "success", "error": None,
            "release_id": release.name, "spec_digest": digest, "branch": branch,
            "commit": commit, "site_root": str(site.resolve()),
        }),
        encoding="utf-8",
    )


class EvidenceResolverTests(unittest.TestCase):
    def test_item_manifest_does_not_claim_missing_document_pages(self) -> None:
        from types import SimpleNamespace

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            resolver = EvidenceResolver(
                {"slug": "sample", "projectPath": "ReasBook/Books/Sample", "branches": []},
                project_root=root, data_root=root,
            )
            evidence = SimpleNamespace(
                release_id="release", branch="v4.30.0", commit="abc",
                source_available=True, docs_available=True, site_available=True,
                graph_available=False,
            )
            with patch.object(resolver, "resolve", return_value=evidence), \
                 patch.object(resolver, "docs_path", return_value=None), \
                 patch.object(resolver, "verso_path", return_value=None), \
                 patch.object(resolver, "source_path", return_value=None):
                book = resolver.manifest("/api/books/sample")
                item = resolver.manifest("/api/books/sample", {"sourcePath": "Missing.lean"})
            self.assertTrue(book["verso"]["available"])
            self.assertTrue(book["source"]["available"])
            self.assertFalse(item["source"]["available"])
            for kind in ("docs", "verso"):
                self.assertFalse(item[kind]["available"])
                self.assertEqual(item[kind]["url"], "")

    def test_typed_compiled_graph_outranks_equal_legacy_union_graph(self) -> None:
        legacy = {
            "schemaVersion": 1,
            "generation": {"mode": "lean-environment"},
            "items": [{"id": "target", "dependencies": ["base"]}],
        }
        typed = {
            "schemaVersion": 2,
            "generation": {
                "mode": "lean-environment",
                "dependencyModel": "statement-and-proof-v1",
            },
            "items": [
                {
                    "id": "target",
                    "statementDependencies": ["base"],
                    "proofDependencies": [],
                    "dependencies": ["base"],
                }
            ],
        }

        self.assertGreater(
            EvidenceResolver._graph_quality(typed),
            EvidenceResolver._graph_quality(legacy),
        )

    def test_typed_partial_graph_is_an_eligible_release_cache(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            data_root = root / "data"
            cache = data_root / "books/sample_book/theorem-map"
            cache.mkdir(parents=True)
            (cache / "index.html").write_text("<html></html>", encoding="utf-8")
            (cache / "data.json").write_text(
                json.dumps(
                    {
                        "schemaVersion": 2,
                        "project": {
                            "id": "Sample_Book",
                            "kind": "books",
                            "branch": "v4.30.0",
                            "commit": "release-commit",
                        },
                        "generation": {
                            "mode": "lean-environment-partial",
                            "dependencyModel": "statement-and-proof-v1",
                            "dependencyCoverage": "partial",
                        },
                        "items": [
                            {
                                "id": "theorem-1",
                                "statementDependencies": [],
                                "proofDependencies": [],
                                "dependencies": [],
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            resolver = EvidenceResolver(
                {
                    "slug": "sample_book",
                    "kind": "book",
                    "projectPath": "ReasBook/Books/Sample_Book",
                    "branches": ["v4.30.0"],
                },
                project_root=root,
                data_root=data_root,
            )

            cached = resolver._cached_graph("sample_book", "release-commit")

            self.assertIsNotNone(cached)

    def test_generic_and_curated_graphs_reuse_renderer_with_original_assets_available(self) -> None:
        from types import SimpleNamespace

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            original = root / "app.js"
            original.write_text("// curated renderer", encoding="utf-8")
            resolver = EvidenceResolver(
                {"slug": "sample", "projectPath": "ReasBook/Books/Sample", "branches": []},
                project_root=root, data_root=root,
            )
            evidence = SimpleNamespace(graph_root=root, site_root=root, docs_root=root)
            with patch.object(resolver, "resolve", return_value=evidence):
                resolver._graph_payload = {"schemaVersion": 2, "generation": {"mode": "lean-environment"}}
                resolved = resolver.evidence_file("graph", "app.js")
                self.assertEqual(resolved[0], GRAPH_ASSETS / "app.js")
                self.assertEqual(original.read_text(), "// curated renderer")
                resolver._graph_payload = {"schemaVersion": 1, "generation": {"mode": "curated-static"}, "items": []}
                self.assertEqual(resolver.evidence_file("graph", "app.js")[0], GRAPH_ASSETS / "app.js")
                self.assertEqual(resolver.evidence_file("graph", "original/app.js")[0], original)
                self.assertIsNone(resolver.evidence_file("graph", "original/../../outside"))
                resolver._graph_payload = {"schemaVersion": 1, "items": []}
                self.assertEqual(resolver.evidence_file("graph", "app.js")[0], original)
                self.assertIsNone(resolver.evidence_file("graph", "../../outside"))

    def test_declaration_assignment_skips_let_binding(self) -> None:
        block = """lemma sample :
    let E : Set ℝ := Set.Ico (1 : ℝ) 2
    ; E = E :=
by
  rfl"""
        assignment = _declaration_assignment(block)
        self.assertEqual(block[assignment:], ":=\nby\n  rfl")

    def test_docs_source_links_post_message_to_the_parent_reviewer(self) -> None:
        html = (
            '<html><body><a href="https://github.com/optpku/ReasBook/blob/abc/'
            'ReasBook/Books/Sample_Book/Chap01/Example.lean#L42">source</a></body></html>'
        )
        rewritten = rewrite_html_for_proxy(
            html,
            kind="docs",
            prefix="/api/books/sample_book/evidence/docs",
            project_id="Sample_Book",
            project_kind="books",
        )
        self.assertIn('type: "reasbook-source-jump"', rewritten)
        self.assertIn("sourcePath: decodeURIComponent", rewritten)
        self.assertIn("/ReasBook/Books/Sample_Book/", rewritten)

    def test_verso_docs_links_use_the_docs_proxy(self) -> None:
        html = (
            '<base href="/ReasBook/versions/v4.30.0/">'
            '<script>window.__versoSiteRoot="/ReasBook/versions/v4.30.0/"</script>'
            '<a href="/ReasBook/versions/v4.30.0/docs/ReasBook/find?pattern=Foo#doc">Foo</a>'
            '<a href="/ReasBook/versions/v4.30.0/analysis2_tao_2022/chap01/">Chapter</a>'
        )
        rewritten = rewrite_html_for_proxy(
            html,
            kind="verso",
            prefix="/api/books/analysis2_tao_2022/evidence/verso",
            docs_prefix="/api/books/analysis2_tao_2022/evidence/documentation",
            branch="v4.30.0",
        )
        self.assertIn("/api/books/analysis2_tao_2022/evidence/documentation/find/?pattern=Foo#doc", rewritten)
        self.assertIn("/api/books/analysis2_tao_2022/evidence/verso/analysis2_tao_2022/chap01/", rewritten)
        self.assertIn('window.__versoSiteRoot="/api/books/analysis2_tao_2022/evidence/"', rewritten)
        self.assertNotIn("/evidence/verso/docs/ReasBook/", rewritten)

    def test_verso_links_preserve_an_unknown_outer_proxy_prefix(self) -> None:
        html = (
            '<base href="/ReasBook/versions/v4.30.0/">'
            '<script>window.__versoSiteRoot="/ReasBook/versions/v4.30.0/"</script>'
            '<link href="/ReasBook/versions/v4.30.0/static/style.css">'
            '<a href="/ReasBook/versions/v4.30.0/docs/ReasBook/find?pattern=Foo#doc">Foo</a>'
            '<a href="/ReasBook/versions/v4.30.0/analysis2_tao_2022/chap01/">Chapter</a>'
        )
        rewritten = rewrite_html_for_proxy(
            html,
            kind="verso",
            prefix="/api/books/analysis2_tao_2022/evidence/verso",
            docs_prefix="/api/books/analysis2_tao_2022/evidence/documentation",
            relative_base="../../../",
            branch="v4.30.0",
        )
        self.assertIn('<base href="../../../" />', rewritten)
        self.assertIn('window.__versoSiteRoot=""', rewritten)
        self.assertIn('href="static/style.css"', rewritten)
        self.assertIn('href="../documentation/find/?pattern=Foo#doc"', rewritten)
        self.assertIn('href="analysis2_tao_2022/chap01/"', rewritten)
        self.assertNotIn('href="/api/', rewritten)

    def test_release_commit_repairs_stale_index_source_pairing(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            release_root = root / "releases"
            old_release = release_root / "site-old"
            new_release = release_root / "site-new"
            old_source = old_release / "worktrees" / "v4.30.0" / "ReasBook" / "Books" / "Sample_Book"
            source_file = old_source / "Chapter.lean"
            source_file.parent.mkdir(parents=True)
            source_file.write_text("theorem sample : True := by trivial\n", encoding="utf-8")
            marker = old_release / "worktrees" / "v4.30.0" / ".reasbook-release-source.json"
            marker.write_text(json.dumps({"commit": "release-commit"}), encoding="utf-8")

            site = new_release / "branches" / "v4.30.0" / "site"
            (site / "docs" / "ReasBook").mkdir(parents=True)
            (new_release / "release-spec.json").write_text(
                json.dumps(
                    {
                        "projects": [
                            {
                                "branch": "v4.30.0",
                                "commit": "release-commit",
                                "project_id": "Sample_Book",
                                "slug": "sample_book",
                            }
                        ]
                    }
                ),
                encoding="utf-8",
            )
            _mark_release_success(new_release, branch="v4.30.0", commit="release-commit")

            data_root = root / "data"
            index_dir = data_root / "books" / "sample_book"
            index_dir.mkdir(parents=True)
            (index_dir / "index.json").write_text(
                json.dumps({"branch": "v4.30.0", "commit": "stale-index-commit"}),
                encoding="utf-8",
            )
            os.utime(old_release, (1, 1))
            os.utime(new_release, (2, 2))

            book = {
                "slug": "sample_book",
                "kind": "book",
                "projectPath": "ReasBook/Books/Sample_Book",
                "branches": ["v4.30.0"],
            }
            with patch.dict(os.environ, {"REASBOOK_REVIEWER_RELEASE_ROOT": str(release_root)}):
                resolver = EvidenceResolver(book, project_root=root, data_root=data_root)
                evidence = resolver.resolve()

            self.assertIsNotNone(evidence)
            assert evidence is not None
            self.assertEqual(evidence.commit, "release-commit")
            self.assertTrue(evidence.source_available)
            self.assertEqual(resolver.source_path("Chapter.lean"), source_file.resolve())

    def test_matching_compiled_graph_replaces_source_fallback_graph(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            release_root = root / "releases"
            release = release_root / "site-current"
            release_graph = release / "branches" / "v4.30.0" / "site" / "theorem-maps" / "books" / "sample_book"
            release_graph.mkdir(parents=True)
            (release_graph / "index.html").write_text("<html></html>", encoding="utf-8")
            (release_graph / "data.json").write_text(
                json.dumps(
                    {
                        "project": {
                            "id": "Sample_Book",
                            "kind": "books",
                            "branch": "v4.30.0",
                            "commit": "release-commit",
                        },
                        "generation": {"mode": "source-fallback"},
                        "items": [
                            {
                                "id": "theorem-1",
                                "declaration": "Sample.target",
                                "file": "Chapter.lean",
                                "line": 12,
                                "dependencies": [],
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            (release / "release-spec.json").write_text(
                json.dumps(
                    {
                        "projects": [
                            {
                                "branch": "v4.30.0",
                                "commit": "release-commit",
                                "project_id": "Sample_Book",
                                "slug": "sample_book",
                            }
                        ]
                    }
                ),
                encoding="utf-8",
            )
            _mark_release_success(release, branch="v4.30.0", commit="release-commit")

            data_root = root / "data"
            cache = data_root / "books" / "sample_book" / "theorem-map"
            cache.mkdir(parents=True)
            (cache / "index.html").write_text("<html></html>", encoding="utf-8")
            (cache / "data.json").write_text(
                json.dumps(
                    {
                        "schemaVersion": 2,
                        "project": {
                            "id": "Sample_Book",
                            "kind": "books",
                            "branch": "v4.30.0",
                            "commit": "release-commit",
                        },
                        "generation": {"mode": "lean-environment"},
                        "items": [
                            {
                                "id": "definition-1",
                                "declaration": "Sample.base",
                                "file": "Chapter.lean",
                                "line": 4,
                                "statementDependencies": [],
                                "proofDependencies": [],
                                "dependencies": [],
                            },
                            {
                                "id": "theorem-1",
                                "declaration": "Sample.target",
                                "file": "Chapter.lean",
                                "line": 12,
                                "statementDependencies": ["definition-1"],
                                "proofDependencies": [],
                                "dependencies": ["definition-1"],
                            },
                            {
                                "id": "theorem-2",
                                "declaration": "Sample.consumer",
                                "file": "Chapter.lean",
                                "line": 20,
                                "statementDependencies": [],
                                "proofDependencies": ["theorem-1"],
                                "dependencies": ["theorem-1"],
                            },
                            {
                                "id": "theorem-3",
                                "declaration": "Sample.sourceOnly",
                                "file": "Omitted.lean",
                                "line": 7,
                                "statementDependencies": [],
                                "proofDependencies": [],
                                "dependencies": [],
                                "dependencyEvidence": "source-only",
                            },
                        ],
                    }
                ),
                encoding="utf-8",
            )
            book = {
                "slug": "sample_book",
                "kind": "book",
                "projectPath": "ReasBook/Books/Sample_Book",
                "branches": ["v4.30.0"],
            }
            with patch.dict(os.environ, {"REASBOOK_REVIEWER_RELEASE_ROOT": str(release_root)}):
                resolver = EvidenceResolver(book, project_root=root, data_root=data_root)
                evidence = resolver.resolve()
                graph = resolver.graph_for_item({"sourcePath": "Chapter.lean", "name": "Sample.target", "line": 12})
                source_only_graph = resolver.graph_for_item(
                    {
                        "sourcePath": "Omitted.lean",
                        "name": "Sample.sourceOnly",
                        "line": 7,
                    }
                )

            self.assertIsNotNone(evidence)
            assert evidence is not None
            self.assertEqual(evidence.graph_path, (cache / "data.json").resolve())
            self.assertEqual(graph["generation"]["mode"], "lean-environment")
            self.assertEqual(graph["totalEdges"], 2)
            self.assertEqual({node["id"] for node in graph["nodes"]}, {"definition-1", "theorem-1", "theorem-2"})
            self.assertEqual(
                {(edge["source"], edge["target"]) for edge in graph["edges"]},
                {("definition-1", "theorem-1"), ("theorem-1", "theorem-2")},
            )
            self.assertEqual([node["declaration"] for node in graph["upstream"]], ["Sample.base"])
            self.assertEqual([node["declaration"] for node in graph["downstream"]], ["Sample.consumer"])
            self.assertTrue(graph["typedDependencies"])
            self.assertEqual(graph["upstream"][0]["kinds"], ["statement"])
            self.assertEqual(graph["downstream"][0]["kinds"], ["proof"])
            self.assertEqual(graph["selectedDependencyEvidence"], "compiled")
            self.assertEqual(
                source_only_graph["selectedDependencyEvidence"], "source-only"
            )

    def test_stale_compiled_graph_does_not_cross_release_commits(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            release_root = root / "releases"
            release = release_root / "site-current"
            release_graph = release / "branches" / "v4.30.0" / "site" / "theorem-maps" / "books" / "sample_book"
            release_graph.mkdir(parents=True)
            (release_graph / "index.html").write_text("<html></html>", encoding="utf-8")
            (release_graph / "data.json").write_text(
                json.dumps(
                    {
                        "project": {"id": "Sample_Book", "kind": "books", "branch": "v4.30.0"},
                        "generation": {"mode": "source-fallback"},
                        "items": [],
                    }
                ),
                encoding="utf-8",
            )
            (release / "release-spec.json").write_text(
                json.dumps(
                    {
                        "projects": [
                            {
                                "branch": "v4.30.0",
                                "commit": "current-commit",
                                "project_id": "Sample_Book",
                                "slug": "sample_book",
                            }
                        ]
                    }
                ),
                encoding="utf-8",
            )
            _mark_release_success(release, branch="v4.30.0", commit="current-commit")
            data_root = root / "data"
            cache = data_root / "books" / "sample_book" / "theorem-map"
            cache.mkdir(parents=True)
            (cache / "index.html").write_text("<html></html>", encoding="utf-8")
            (cache / "data.json").write_text(
                json.dumps(
                    {
                        "project": {
                            "id": "Sample_Book",
                            "kind": "books",
                            "branch": "v4.30.0",
                            "commit": "stale-commit",
                        },
                        "generation": {"mode": "lean-environment"},
                        "items": [{"id": "old", "dependencies": ["older"]}],
                    }
                ),
                encoding="utf-8",
            )
            book = {
                "slug": "sample_book",
                "kind": "book",
                "projectPath": "ReasBook/Books/Sample_Book",
                "branches": ["v4.30.0"],
            }
            with patch.dict(os.environ, {"REASBOOK_REVIEWER_RELEASE_ROOT": str(release_root)}):
                resolver = EvidenceResolver(book, project_root=root, data_root=data_root)
                evidence = resolver.resolve()

            self.assertIsNotNone(evidence)
            assert evidence is not None
            self.assertIsNone(evidence.graph_path)


if __name__ == "__main__":
    unittest.main()
