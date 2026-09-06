from __future__ import annotations

import importlib.util
import hashlib
import json
import os
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
import sys
from unittest.mock import patch

from fastapi import HTTPException
from fastapi.testclient import TestClient

PROJECT_ROOT = Path(__file__).resolve().parents[1]
IMPORT_STATE = tempfile.TemporaryDirectory()
FIXTURE_ROOT = Path(IMPORT_STATE.name)
FIXTURE_DATA = FIXTURE_ROOT / "data"
FIXTURE_RELEASES = FIXTURE_ROOT / "releases"


def _fixture_file(path: Path, content: str | dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(content) if isinstance(content, dict) else content, encoding="utf-8")


def _prepare_fixture() -> None:
    slug = "analysis2_tao_2022"
    project = "Analysis2_Tao_2022"
    source_path = "Chap01/Example.lean"
    item = {
        "key": "Analysis2.chapter1.theorem1", "name": "Sample.example", "kind": "theorem",
        "sourcePath": source_path, "line": 1, "title": "A fixture theorem",
    }
    books = []
    for book_slug, kind in ((slug, "book"), ("empty_paper", "paper")):
        books.append({
            "slug": book_slug, "title": book_slug, "kind": kind,
            "projectPath": f"ReasBook/Books/{project}" if kind == "book" else "ReasBook/Papers/Empty",
            "branches": ["v4.30.0"] if kind == "book" else [],
            "reviewIndex": {"state": "ready" if kind == "book" else "not-built"},
            "artifacts": {name: {"path": f"data/books/{book_slug}/{name}.json", "state": "not-built"}
                          for name in ("index", "source", "docs", "graphs")},
        })
    _fixture_file(FIXTURE_DATA / "catalog.json", {"schemaVersion": 1, "books": books})
    _fixture_file(FIXTURE_DATA / "books" / slug / "index.json", {"state": "ready", "items": [item]})
    release = FIXTURE_RELEASES / "fixture"
    site = release / "branches/v4.30.0/site"
    _fixture_file(release / "release-spec.json", {"projects": [{
        "slug": slug, "project_id": project, "branch": "v4.30.0", "commit": "fixture-commit",
    }], "branches": [{"name": "v4.30.0", "commit": "fixture-commit"}],
        "release_id": "fixture", "spec_digest": "sha256:" + hashlib.sha256(b"fixture").hexdigest()})
    _fixture_file(release / "branches/v4.30.0/result.json", {
        "schema_version": 1, "status": "success", "error": None,
        "release_id": "fixture", "spec_digest": "sha256:" + hashlib.sha256(b"fixture").hexdigest(),
        "branch": "v4.30.0", "commit": "fixture-commit", "site_root": str(site.resolve()),
    })
    _fixture_file(release / "worktrees/v4.30.0/ReasBook/Books" / project / source_path,
                  "theorem Sample.example : True := by\n  trivial\n")
    _fixture_file(site / "docs/ReasBook" / project / "Chap01/Example.html",
                  '<html><body><div id="Sample.example">Example docs</div></body></html>')
    _fixture_file(site / slug / "index.html", "<html><body>Example Verso</body></html>")
    _fixture_file(site / slug / "chap01/example/index.html", "<html><body>Example Verso statement</body></html>")
    graph_root = site / "theorem-maps/books" / slug
    _fixture_file(graph_root / "index.html", "<html><body>Graph fixture</body></html>")
    _fixture_file(graph_root / "data.json", {
        "schemaVersion": 2,
        "generation": {"mode": "lean-environment", "dependencyModel": "statement-and-proof-v1"},
        "items": [{"id": "example", "declaration": "Sample.example", "file": source_path,
                   "line": 1, "dependencies": [], "statementDependencies": [], "proofDependencies": []}],
    })


_prepare_fixture()
_ENV_KEYS = (
    "REASLAB_OAUTH_ISSUER",
    "REASLAB_OAUTH_CLIENT_ID",
    "REASLAB_OAUTH_CLIENT_SECRET",
    "REASLAB_OAUTH_REDIRECT_URI",
    "REASBOOK_REVIEWER_CATALOG",
    "REASBOOK_REVIEWER_DATA",
    "REASBOOK_REVIEWER_DB",
    "REASBOOK_ROOT",
    "REASLAB_AUTH_ROOT",
    "REASBOOK_PUBLIC_ARTIFACTS",
    "REASBOOK_ADMIN_SUBJECTS",
    "REASBOOK_REVIEWER_BOOK_DATA",
    "REASBOOK_REVIEWER_RELEASE_ROOT",
)
_SAVED_ENV = {key: os.environ.get(key) for key in _ENV_KEYS}
for _key in _ENV_KEYS:
    os.environ.pop(_key, None)
os.environ["REASBOOK_REVIEWER_DB"] = str(Path(IMPORT_STATE.name) / "import.sqlite3")
os.environ["REASBOOK_REVIEWER_DATA"] = str(FIXTURE_DATA)
os.environ["REASBOOK_REVIEWER_CATALOG"] = str(FIXTURE_DATA / "catalog.json")
os.environ["REASBOOK_REVIEWER_RELEASE_ROOT"] = str(FIXTURE_RELEASES)

SPEC = importlib.util.spec_from_file_location("reasbook_reviewer_app", PROJECT_ROOT / "app.py")
assert SPEC is not None and SPEC.loader is not None
reviewer_app = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = reviewer_app
with patch("catalog.default_reasbook_root", return_value=FIXTURE_ROOT):
    SPEC.loader.exec_module(reviewer_app)
for _key, _value in _SAVED_ENV.items():
    if _value is None:
        os.environ.pop(_key, None)
    else:
        os.environ[_key] = _value


class _FakeAuth:
    def __init__(self) -> None:
        self.session = SimpleNamespace(
            subject="reaslab-user-42",
            name="Test Reviewer",
            email="reviewer@example.test",
        )

    def get_session(self, request):
        return self.session

    def validate_csrf(self, request, session) -> None:
        if session is not self.session or request.headers.get("X-CSRF-Token") != "csrf-token":
            raise HTTPException(status_code=403, detail="Invalid CSRF token")


class FrontendContractTests(unittest.TestCase):
    def test_evidence_history_controls_are_wired(self) -> None:
        html = (PROJECT_ROOT / "docs" / "index.html").read_text(encoding="utf-8")
        script = (PROJECT_ROOT / "docs" / "app.js").read_text(encoding="utf-8")
        styles = (PROJECT_ROOT / "docs" / "styles.css").read_text(encoding="utf-8")
        self.assertIn('id="evidenceHistoryControls"', html)
        self.assertIn('id="evidenceBack"', html)
        self.assertIn('id="evidenceForward"', html)
        self.assertIn("function navigateEvidenceHistory", script)
        self.assertIn("frame.contentWindow.history.go(direction)", script)
        self.assertIn("evidenceReturn", script)
        self.assertIn("function focusDocsDeclaration", script)
        self.assertIn("function focusVersoDeclaration", script)
        self.assertIn("docsTarget.hash = encodeURIComponent(item.name)", script)
        self.assertIn('id="detailStatementLabel"', html)
        self.assertIn('id="detailKind" class="eyebrow detail-kind"', html)
        self.assertNotIn('id="graphScopeControls"', html)
        self.assertNotIn('id="detailPath"', html)
        self.assertIn("function statementParts", script)
        self.assertIn("const flushParagraph = () =>", script)
        self.assertIn("const standaloneMatch = text.match", script)
        self.assertIn("function leanMathToTex", script)
        self.assertIn("const symbols =", script)
        self.assertIn("const parse = (closing", script)
        self.assertIn("statement-inline-code", script)
        self.assertIn("function displayStatementHeading", script)
        self.assertIn('id="statementSourceToggle"', html)
        self.assertIn('id="copyStatementSource"', html)
        self.assertIn('id="statementSourcePreview"', html)
        self.assertIn("function renderStatementSource", script)
        self.assertIn("async function copyStatementSource", script)
        self.assertIn("navigator.clipboard?.writeText", script)
        self.assertIn('class=\"statement-formula\"', script)
        self.assertIn("function itemLocation", script)
        self.assertIn('class=\"queue-location\"', script)
        self.assertIn("function isStacksBook", script)
        self.assertIn("function stackTags", script)
        self.assertIn("refs.versoTab.hidden = stacksMode", script)
        self.assertIn("stacks-queue-row", script)
        self.assertIn("function selectGraphItemFromFrame", script)
        self.assertIn('closest?.("[data-node-id]")', script)
        self.assertIn("selectGraphItemFromFrame(node.dataset.nodeId, true)", script)
        self.assertIn("function loadedGraphBookSlug", script)
        self.assertIn("loadedSlug !== state.selectedSlug", script)
        self.assertIn("function graphScopePreference", script)
        self.assertIn("function rememberGraphScope", script)
        self.assertIn("function enforceGraphScope", script)
        self.assertIn("reasbook-reviewer:graph-scope-v2:${slug}", script)
        self.assertIn('graphScopePending = "true"', script)
        self.assertIn("function compactOriginalGraphNodes", script)
        self.assertIn("function installOriginalGraphLayoutControls", script)
        self.assertIn("__reasbookTheoremMapLayout", script)
        self.assertIn('button.dataset.layoutMode = mode', script)
        self.assertIn("graphScopeByBook", script)
        self.assertIn("graphDependencyByBook", script)
        self.assertIn("function installOriginalGraphDependencyControls", script)
        self.assertIn("reasbook-reviewer:graph-dependencies:${slug}", script)
        self.assertNotIn('["both", "Both"]', script)
        self.assertNotIn('["all", "All"]', script)
        self.assertIn('["statement-edges", "Stmt edges"]', script)
        self.assertIn('["statement", "Stmt"]', script)
        self.assertIn('id="relationFilters"', html)
        self.assertIn("relationDependencyMode", script)
        self.assertIn('data-relation-mode="statement"', html)
        self.assertIn('data-relation-mode="proof"', html)
        self.assertIn('value="paper">Papers', html)
        self.assertIn('class="catalog-group"', script)
        self.assertIn("__reasbookTheoremMapDependencies?.setMode(normalized)", script)
        self.assertNotIn('body[data-dependency-filter="statement"] .graph-edge', script)
        self.assertIn(".toolbar-title { display: none !important; }", script)
        self.assertIn(".graph-scope-heading > .segmented { display: inline-flex !important; }", script)
        self.assertIn("function alignReaderControls", script)
        self.assertNotIn("Compiled dependency graph", script)
        self.assertNotIn("graph.totalEdges", script)
        self.assertIn("Compiled · statement / proof edges", script)
        self.assertIn("Source index · dependency evidence unavailable", script)
        self.assertNotIn("item.module ?", script)
        self.assertIn("white-space: normal", styles)
        self.assertIn("height: 100vh; height: 100dvh", styles)
        self.assertIn('id="catalogResize"', html)
        self.assertIn('id="queueResize"', html)
        self.assertIn('id="reviewResize"', html)
        self.assertIn("function bindPaneResizer", script)
        self.assertNotIn('id="toggleCanvas"', html)
        self.assertIn('id="relationSection" class="relation-section"', html)
        self.assertIn("refs.detailTitle.textContent = displayStatementHeading", script)
        self.assertIn('refs.reviewControls.hidden = false', script)


class AuthCookiePathTests(unittest.TestCase):
    def test_login_return_uses_cookie_scope_for_both_gateway_aliases(self):
        prefix = "/siflow/changliu/hash/reasbook-reviewer/v1/8000/ReasBook/"
        alias = "/siflow/changliu/tenant/user/reasbook-reviewer/v1/8000"
        normalize = reviewer_app._canonical_auth_return_to
        self.assertEqual(normalize(alias, prefix), prefix)
        self.assertEqual(normalize(alias + "/ReasBook/books/may/?item=definition", prefix),
                         prefix + "books/may/?item=definition")
        self.assertEqual(normalize(prefix + "books/may/?item=definition", prefix),
                         prefix + "books/may/?item=definition")
        for unsafe in ("https://evil.example/", "//evil.example/", "/ReasBook/../other/", "/ReasBook/%2e%2e/other/"):
            self.assertEqual(normalize(unsafe, prefix), prefix)

    def test_shared_gateway_cookie_scope_and_deletion(self):
        from fastapi.responses import Response
        response = Response()
        response.set_cookie("transaction", "opaque", path="/api/auth/oauth", secure=True, httponly=True)
        response.set_cookie("session", "opaque", path="/", secure=True, httponly=True)
        response.delete_cookie("expired", path="/api/auth/oauth")
        prefix = "/siflow/changliu/service/ReasBook/"
        with patch.dict(os.environ, {"REASBOOK_AUTH_COOKIE_PATH": prefix}):
            reviewer_app._rewrite_auth_cookie_paths(response)
        cookies = response.headers.getlist("set-cookie")
        self.assertEqual(len(cookies), 3)
        self.assertTrue(all(f"Path={prefix}" in value for value in cookies))
        self.assertIn("Secure", cookies[0])
        self.assertIn("HttpOnly", cookies[0])

    def test_login_middleware_passes_canonical_return_to_to_auth_router(self):
        from fastapi import FastAPI
        fixture = FastAPI()
        fixture.middleware("http")(reviewer_app.security_headers)

        @fixture.get("/api/auth/oauth/start")
        async def start(return_to: str):
            return {"return_to": return_to}

        prefix = "/service/hash/ReasBook/"
        with patch.dict(os.environ, {"REASBOOK_AUTH_COOKIE_PATH": prefix}), TestClient(fixture) as client:
            response = client.get("/api/auth/oauth/start", params={"return_to": "/service/alias/ReasBook/books/may/?item=lemma"})
        self.assertEqual(response.json(), {"return_to": prefix + "books/may/?item=lemma"})

    def test_default_and_invalid_cookie_scope(self):
        from fastapi.responses import Response
        response = Response()
        response.set_cookie("transaction", "opaque", path="/api/auth/oauth")
        with patch.dict(os.environ, {"REASBOOK_AUTH_COOKIE_PATH": "/"}):
            reviewer_app._rewrite_auth_cookie_paths(response)
        self.assertIn("Path=/;", response.headers["set-cookie"])
        with patch.dict(os.environ, {"REASBOOK_AUTH_COOKIE_PATH": "/; injected=yes"}):
            with self.assertRaises(ValueError):
                reviewer_app._rewrite_auth_cookie_paths(response)


class ResolverCacheTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name) / "published-data"
        self.slug = "analysis2_tao_2022"
        self.index = root / "books" / self.slug / "custom-index.json"
        _fixture_file(self.index, {"branch": "v4.30.0", "commit": "first"})
        original = reviewer_app.BOOKS_BY_SLUG[self.slug]
        book = {**original, "artifacts": {
            **original["artifacts"], "index": {"path": f"data/books/{self.slug}/custom-index.json"},
        }}
        for context in (
            patch.object(reviewer_app, "DATA_ROOT", root),
            patch.object(reviewer_app, "BOOK_DATA_ROOT", root / "books"),
            patch.dict(reviewer_app.BOOKS_BY_SLUG, {self.slug: book}),
        ):
            context.start()
            self.addCleanup(context.stop)
        clock = patch.object(reviewer_app, "monotonic", return_value=100.0)
        self.clock = clock.start()
        self.addCleanup(clock.stop)
        reviewer_app.RESOURCE_RESOLVERS.clear()
        self.addCleanup(reviewer_app.RESOURCE_RESOLVERS.clear)

    def test_resolver_reuses_until_exact_ttl_and_clears_cached_graph(self) -> None:
        first = reviewer_app._resolver_for(self.slug)
        self.assertEqual(first.branch, "v4.30.0")
        self.assertEqual(first.requested_commit, "first")
        self.assertEqual(first.index_path, self.index)
        first._graph_payload = {"items": [{"id": "old-release"}]}
        first._evidence = object()
        self.clock.return_value = 159.999
        self.assertIs(reviewer_app._resolver_for(self.slug), first)
        self.clock.return_value = 160.0
        refreshed = reviewer_app._resolver_for(self.slug)
        self.assertIsNot(refreshed, first)
        self.assertIsNone(refreshed._graph_payload)
        self.assertIsNone(refreshed._evidence)
        self.assertIs(reviewer_app._resolver_for(self.slug), refreshed)
        reviewer_app.RESOURCE_RESOLVERS.clear()
        self.assertIsNot(reviewer_app._resolver_for(self.slug), refreshed)

    def test_atomic_index_swap_refreshes_immediately_even_same_size_and_mtime(self) -> None:
        first = reviewer_app._resolver_for(self.slug)
        before = self.index.stat()
        replacement = self.index.with_suffix(".next")
        _fixture_file(replacement, {"branch": "v4.31.0", "commit": "other"})
        os.utime(replacement, ns=(before.st_atime_ns, before.st_mtime_ns))
        self.assertEqual(replacement.stat().st_size, before.st_size)
        replacement.replace(self.index)
        refreshed = reviewer_app._resolver_for(self.slug)
        self.assertIsNot(refreshed, first)
        self.assertEqual(refreshed.branch, "v4.31.0")
        self.assertEqual(refreshed.requested_commit, "other")

    def test_missing_index_creation_and_removal_invalidate_without_waiting(self) -> None:
        self.index.unlink()
        missing = reviewer_app._resolver_for(self.slug)
        self.assertEqual(missing.requested_commit, "")
        _fixture_file(self.index, {"branch": "v4.31.0", "commit": "new"})
        present = reviewer_app._resolver_for(self.slug)
        self.assertIsNot(present, missing)
        self.assertEqual(present.requested_commit, "new")
        self.index.unlink()
        self.assertIsNot(reviewer_app._resolver_for(self.slug), present)


class ApiTests(unittest.TestCase):
    def setUp(self) -> None:
        env = patch.dict(os.environ, {"REASBOOK_REVIEWER_RELEASE_ROOT": str(FIXTURE_RELEASES)})
        env.start()
        self.addCleanup(env.stop)
        reviewer_app.RESOURCE_RESOLVERS.clear()
        self.client = TestClient(reviewer_app.app)

    def test_public_history_hides_transport_metadata_and_export_requires_admin(self) -> None:
        slug = "analysis2_tao_2022"
        key = "Analysis2.chapter1.theorem1"
        with tempfile.TemporaryDirectory() as temp_dir:
            store = reviewer_app.ReviewStore(Path(temp_dir) / "reviews.sqlite3")
            store.save_review(
                slug,
                key,
                {"status": "accepted", "comment": "Public comment", "clientId": "browser", "baseRevision": 0},
                reviewer_app.Actor("author", "Author", None),
                remote_addr="192.0.2.42",
                user_agent="private-browser-fingerprint",
            )
            auth = _FakeAuth()
            auth.session = None
            with patch.object(reviewer_app, "STORE", store), patch.object(reviewer_app, "AUTH", auth):
                response = self.client.get(f"/api/books/{slug}/reviews/{key}/history")
                self.assertEqual(response.status_code, 200)
                self.assertEqual(response.json()["events"][0]["comment"], "Public comment")
                for private in ("remoteAddr", "userAgent", "192.0.2.42", "private-browser-fingerprint"):
                    self.assertNotIn(private, response.text)
                self.assertEqual(self.client.get("/api/reviews/export.jsonl").status_code, 401)

                auth.session = SimpleNamespace(subject="reader", name="Reader", email=None)
                self.assertEqual(self.client.get("/api/reviews/export.jsonl").status_code, 403)
                with patch.object(reviewer_app, "ADMIN_SUBJECTS", {"reader"}):
                    for route in ("/api/reviews/export.jsonl", f"/api/books/{slug}/reviews/export.jsonl"):
                        exported = self.client.get(route)
                        self.assertEqual(exported.status_code, 200)
                        event = json.loads(exported.text)
                        self.assertEqual(event["remote_addr"], "192.0.2.42")
                        self.assertEqual(event["user_agent"], "private-browser-fingerprint")

    def test_anonymous_write_to_existing_item_is_rejected_without_persistence(self) -> None:
        auth = _FakeAuth()
        auth.session = None
        with tempfile.TemporaryDirectory() as temp_dir:
            store = reviewer_app.ReviewStore(Path(temp_dir) / "reviews.sqlite3")
            with (
                patch.object(reviewer_app, "STORE", store),
                patch.object(reviewer_app, "AUTH", auth),
                patch.object(reviewer_app, "_review_items", return_value=({"state": "ready"}, [{"key": "theorem"}])),
            ):
                response = self.client.post(
                    "/api/books/analysis2_tao_2022/reviews/theorem",
                    json={"status": "accepted", "comment": "", "clientId": "client", "baseRevision": 0},
                )
                self.assertEqual(response.status_code, 401)
                self.assertEqual(store.list_events(), [])

    def test_authenticated_malformed_requests_do_not_write_reviews(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            store = reviewer_app.ReviewStore(Path(temp_dir) / "reviews.sqlite3")
            with (
                patch.object(reviewer_app, "STORE", store),
                patch.object(reviewer_app, "AUTH", _FakeAuth()),
                patch.object(reviewer_app, "_review_items", return_value=({"state": "ready"}, [{"key": "theorem"}])),
            ):
                for content in (b'{"comment":"\xff"}', b'{"baseRevision":1e999,"status":"accepted","clientId":"client"}'):
                    with self.subTest(content=content):
                        response = self.client.post(
                            "/api/books/analysis2_tao_2022/reviews/theorem",
                            content=content,
                            headers={"X-CSRF-Token": "csrf-token", "Content-Type": "application/json"},
                        )
                        self.assertEqual(response.status_code, 400)
                oversized = self.client.post(
                    "/api/books/analysis2_tao_2022/reviews/theorem",
                    content=b" " * (reviewer_app.MAX_BODY_BYTES + 1),
                    headers={"X-CSRF-Token": "csrf-token", "Content-Type": "application/json"},
                )
                self.assertEqual(oversized.status_code, 413)
                self.assertEqual(store.list_events(), [])

    def test_private_evidence_gates_all_routes_including_cached_fallbacks(self) -> None:
        prefix = "/api/books/analysis2_tao_2022"
        protected = (
            "/graph", "/context/Analysis2.chapter1.theorem1",
            "/evidence/documentation/Analysis2_Tao_2022/Chap01/Example.html",
            "/evidence/graph/index.html", "/evidence/graph/vendor/viz-global.js",
            "/artifacts/graphs", "/artifacts/source", "/artifacts/docs",
        )
        anonymous_auth = _FakeAuth()
        anonymous_auth.session = None
        for auth, expected in ((None, 503), (anonymous_auth, 401)):
            with patch.object(reviewer_app, "PUBLIC_ARTIFACTS", False), patch.object(reviewer_app, "AUTH", auth):
                for route in protected:
                    with self.subTest(route=route, auth_configured=auth is not None):
                        self.assertEqual(self.client.get(prefix + route).status_code, expected)
                self.assertEqual(self.client.get(prefix + "/index").status_code, 200)
                self.assertEqual(self.client.get(prefix + "/artifacts/index").status_code, 200)
        for public, auth in ((True, None), (False, _FakeAuth())):
            with patch.object(reviewer_app, "PUBLIC_ARTIFACTS", public), patch.object(reviewer_app, "AUTH", auth):
                for route in protected:
                    with self.subTest(route=route, public=public):
                        self.assertEqual(self.client.get(prefix + route).status_code, 200)
        health = self.client.get("/api/health").json()
        self.assertEqual(health["database"], "sqlite")

    def test_missing_public_name_does_not_publish_oauth_email(self) -> None:
        auth = _FakeAuth()
        auth.session.name = None
        with tempfile.TemporaryDirectory() as temp_dir:
            store = reviewer_app.ReviewStore(Path(temp_dir) / "reviews.sqlite3")
            with patch.object(reviewer_app, "STORE", store), patch.object(reviewer_app, "AUTH", auth):
                route = "/api/books/analysis2_tao_2022/reviews/Analysis2.chapter1.theorem1"
                saved = self.client.post(
                    route,
                    json={"status": "accepted", "comment": "A public comment", "clientId": "browser", "baseRevision": 0},
                    headers={"X-CSRF-Token": "csrf-token"},
                )
                self.assertEqual(saved.status_code, 200)
                self.assertEqual(saved.json()["review"]["reviewer"], "Reader")
                history = self.client.get(route + "/history")
                self.assertNotIn(auth.session.email, history.text)

    def test_catalog_and_empty_book_scaffold(self) -> None:
        catalog = self.client.get("/api/catalog")
        self.assertEqual(catalog.status_code, 200)
        self.assertEqual(len(catalog.json()["books"]), 2)
        self.assertEqual(
            len([book for book in catalog.json()["books"] if book["kind"] == "paper"]),
            1,
        )
        self.assertEqual({book["slug"] for book in catalog.json()["books"]}, {"analysis2_tao_2022", "empty_paper"})
        self.assertEqual(catalog.headers["x-content-type-options"], "nosniff")
        self.assertEqual(self.client.get("/assets/app.js").status_code, 200)
        auth_start = self.client.get("/api/auth/oauth/start")
        self.assertEqual(auth_start.status_code, 503)

        book = self.client.get("/api/books/analysis2_tao_2022")
        self.assertEqual(book.status_code, 200)
        self.assertIn(book.json()["cache"]["state"], {"not-built", "ready"})
        if book.json()["cache"]["state"] == "not-built":
            self.assertEqual(book.json()["items"], [])
        else:
            self.assertGreater(len(book.json()["items"]), 0)
        redirect = self.client.get("/books/analysis2_tao_2022", follow_redirects=False)
        self.assertEqual(redirect.status_code, 307)
        self.assertEqual(redirect.headers["location"], "./analysis2_tao_2022/")
        self.assertEqual(self.client.get("/books/analysis2_tao_2022/assets/app.js").status_code, 200)

        prefixed_without_slash = self.client.get("/ReasBook", follow_redirects=False)
        self.assertEqual(prefixed_without_slash.status_code, 307)
        self.assertEqual(prefixed_without_slash.headers["location"], "./ReasBook/")
        prefixed_index = self.client.get("/ReasBook/")
        self.assertEqual(prefixed_index.status_code, 200)
        self.assertIn("ReasBook Review", prefixed_index.text)
        self.assertEqual(self.client.get("/ReasBook/assets/app.js").status_code, 200)
        self.assertEqual(self.client.get("/ReasBook/api/catalog").status_code, 200)
        prefixed_book = self.client.get("/ReasBook/books/analysis2_tao_2022/")
        self.assertEqual(prefixed_book.status_code, 200)

        artifacts = self.client.get("/api/books/analysis2_tao_2022/artifacts")
        self.assertEqual(artifacts.status_code, 200)
        self.assertEqual(artifacts.json()["artifacts"]["graphs"]["state"], "not-built")
        self.assertEqual(self.client.get("/assets/data/catalog.json").status_code, 404)

        empty = self.client.get("/api/books/empty_paper")
        self.assertEqual(empty.status_code, 200)
        self.assertEqual(empty.json()["items"], [])
        self.assertEqual(empty.json()["cache"]["state"], "not-built")

        write = self.client.post(
            "/api/books/analysis2_tao_2022/reviews/not-generated",
            json={"status": "accepted", "comment": "", "clientId": "client", "baseRevision": 0},
        )
        self.assertEqual(write.status_code, 409)
        self.assertEqual(write.json()["detail"]["code"], "review_index_not_ready")

    def test_statement_context_exposes_release_evidence_when_available(self) -> None:
        book = self.client.get("/api/books/analysis2_tao_2022").json()
        items = book.get("items", [])
        self.assertTrue(items)
        item = items[0]
        resources = self.client.get("/api/books/analysis2_tao_2022/resources")
        self.assertEqual(resources.status_code, 200)
        self.assertIn("resources", resources.json())

        context = self.client.get(
            f"/api/books/analysis2_tao_2022/context/{item['key']}"
        )
        self.assertEqual(context.status_code, 200)
        payload = context.json()
        self.assertEqual(payload["item"]["key"], item["key"])
        self.assertIn("source", payload)
        self.assertIn("lean", payload)
        self.assertTrue(payload["source"].get("available"))
        self.assertTrue(payload["lean"].get("available"))
        self.assertEqual(payload["lean"]["type"], "True")
        self.assertIn("trivial", payload["lean"]["value"])
        self.assertIn("theorem Sample.example", payload["lean"]["code"])
        self.assertIn("graph", payload)
        if payload["resources"].get("docs", {}).get("available"):
            self.assertTrue(payload["resources"]["docs"].get("url"))
        if payload["resources"].get("verso", {}).get("available"):
            self.assertTrue(payload["resources"]["verso"].get("url"))
        if payload["resources"].get("graph", {}).get("available"):
            graph_url = payload["resources"]["graph"].get("url")
            self.assertTrue(graph_url)
            graph_page = self.client.get(graph_url)
            self.assertEqual(graph_page.status_code, 200)
            graph_csp = graph_page.headers["content-security-policy"]
            self.assertIn("'unsafe-eval'", graph_csp)
            self.assertIn("'wasm-unsafe-eval'", graph_csp)
            graph_root = graph_url.rsplit("/", 1)[0]
            for asset in ("app.js", "styles.css", "data.json", "vendor/viz-global.js"):
                self.assertEqual(self.client.get(f"{graph_root}/{asset}").status_code, 200)
            graph_app = self.client.get(f"{graph_root}/app.js")
            self.assertIn("renderReviewerGraphviz", graph_app.text)
            self.assertIn('engine: "dot"', graph_app.text)
            self.assertIn("__reasbookTheoremMapLayout", graph_app.text)
        docs_page = self.client.get(
            "/api/books/analysis2_tao_2022/evidence/documentation/"
            "Analysis2_Tao_2022/Chap01/Example.html"
        )
        self.assertEqual(docs_page.status_code, 200)
        self.assertNotIn("'unsafe-eval'", docs_page.headers["content-security-policy"])

    def test_curated_graph_data_proxy_preserves_reviewed_evidence(self) -> None:
        payload = {
            "schemaVersion": 1,
            "generation": {"mode": "curated-static"},
            "project": {"id": "TR_LALM_theory"},
            "items": [{"id": "lemma-1", "label": "Lemma 1", "section": "deterministic",
                       "title": "Preserved title", "dependencies": [], "dependencyEvidence": "curated"}],
        }
        resolver = SimpleNamespace(graph_payload=lambda: payload)
        with patch.object(reviewer_app, "_resolver_for", return_value=resolver), patch.object(reviewer_app, "PUBLIC_ARTIFACTS", True):
            response = self.client.get("/api/books/analysis2_tao_2022/evidence/graph/data.json")
        self.assertEqual(response.status_code, 200)
        self.assertEqual(response.json(), payload)
        self.assertNotIn("proofDependencies", response.json()["items"][0])

    def test_generated_book_index_uses_reaslab_session_and_csrf(self) -> None:
        # Keep index/source/graph in the same prepared fixture. Changing only
        # BOOK_DATA_ROOT leaves the resolver on DATA_ROOT and mixes evidence.
        with tempfile.TemporaryDirectory() as temp_dir:
            store = reviewer_app.ReviewStore(Path(temp_dir) / "reviews.sqlite3")
            with (
                patch.object(reviewer_app, "STORE", store),
                patch.object(reviewer_app, "AUTH", _FakeAuth()),
                patch.object(reviewer_app, "AUTH_CONFIGURED", True),
            ):
                route = "/api/books/analysis2_tao_2022/reviews/Analysis2.chapter1.theorem1"
                rejected = self.client.post(
                    route,
                    json={"status": "accepted", "comment": "", "clientId": "client", "baseRevision": 0},
                )
                self.assertEqual(rejected.status_code, 403, rejected.text)
                self.assertEqual(store.list_events(), [])
                saved = self.client.post(
                    route,
                    headers={"X-CSRF-Token": "csrf-token"},
                    json={"status": "accepted", "comment": "Matches.", "clientId": "client", "baseRevision": 0},
                )
                self.assertEqual(saved.status_code, 200, saved.text)
                self.assertEqual(saved.json()["review"]["actorId"], "reaslab-user-42")
                conflict = self.client.post(
                    route,
                    headers={"X-CSRF-Token": "csrf-token"},
                    json={"status": "mismatch", "comment": "Stale.", "clientId": "client", "baseRevision": 0},
                )
                self.assertEqual(conflict.status_code, 409, conflict.text)
                self.assertEqual(conflict.json()["error"], "review conflict")
                self.assertEqual(len(store.list_events()), 1)

    def test_portable_catalog_artifact_path_uses_overridden_data_root(self) -> None:
        old_data_root = reviewer_app.DATA_ROOT
        old_book_data_root = reviewer_app.BOOK_DATA_ROOT
        book = reviewer_app.BOOKS_BY_SLUG["analysis2_tao_2022"]
        old_artifact_path = book["artifacts"]["docs"]["path"]
        with tempfile.TemporaryDirectory() as temp_dir:
            data_root = Path(temp_dir) / "published-data"
            book_root = data_root / "books"
            book_dir = book_root / "analysis2_tao_2022"
            book_dir.mkdir(parents=True)
            artifact = book_dir / "custom-docs.json"
            artifact.write_text("{}", encoding="utf-8")
            book["artifacts"]["docs"]["path"] = "data/books/analysis2_tao_2022/custom-docs.json"
            reviewer_app.DATA_ROOT = data_root
            reviewer_app.BOOK_DATA_ROOT = book_root
            try:
                resolved = reviewer_app._artifact_path("analysis2_tao_2022", "docs")
                self.assertEqual(resolved, artifact.resolve())
            finally:
                book["artifacts"]["docs"]["path"] = old_artifact_path
                reviewer_app.DATA_ROOT = old_data_root
                reviewer_app.BOOK_DATA_ROOT = old_book_data_root


if __name__ == "__main__":
    unittest.main()
