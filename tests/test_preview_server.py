from __future__ import annotations

from contextlib import contextmanager
from http.client import HTTPConnection
import importlib.util
from pathlib import Path
import sys
import tempfile
from threading import Thread
import unittest
from urllib.request import urlopen


ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = ROOT / "scripts" / "preview" / "serve.py"
SPEC = importlib.util.spec_from_file_location("reasbook_preview_server", MODULE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load preview server: {MODULE_PATH}")
preview = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = preview
SPEC.loader.exec_module(preview)


@contextmanager
def running_server(
    site: Path,
    public_prefix: str,
    *,
    site_root: str = "/ReasBook/",
):
    old_values = (
        preview.BOOK_SITE,
        preview.DOCS_SITE,
        preview.SITE_ROOT,
        preview.PUBLIC_PREFIX,
    )
    preview.BOOK_SITE = str(site)
    preview.DOCS_SITE = str(site / "docs")
    preview.SITE_ROOT = site_root
    preview.PUBLIC_PREFIX = preview._normalize_public_prefix(public_prefix)
    server = preview.ThreadingHTTPServer(
        ("127.0.0.1", 0), preview.ReasBookHandler
    )
    thread = Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        yield f"http://127.0.0.1:{server.server_port}"
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=5)
        (
            preview.BOOK_SITE,
            preview.DOCS_SITE,
            preview.SITE_ROOT,
            preview.PUBLIC_PREFIX,
        ) = old_values


class PreviewServerTests(unittest.TestCase):
    def test_origin_root_is_served_without_a_redirect_loop(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            site = Path(temp)
            (site / "index.html").write_text(
                "<!doctype html><html><body>Root fixture</body></html>",
                encoding="utf-8",
            )

            with running_server(site, "", site_root="/") as origin:
                with urlopen(origin + "/", timeout=5) as response:
                    self.assertEqual(response.status, 200)
                    self.assertEqual(response.geturl(), origin + "/")
                    self.assertIn("Root fixture", response.read().decode())

            prefix = "/workspace/proxy/3000"
            with running_server(site, prefix, site_root="/") as origin:
                with urlopen(origin + "/", timeout=5) as response:
                    self.assertEqual(response.status, 200)
                    self.assertEqual(response.geturl(), origin + prefix + "/")
                    self.assertIn("Root fixture", response.read().decode())

    def test_reverse_proxy_prefix_rewrites_navigation_and_assets(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            site = Path(temp)
            (site / "static").mkdir()
            (site / "index.html").write_text(
                '<a href="/ReasBook/papers/demo/">Demo</a>'
                '<a href="../../docs/ReasBook/Demo.html">Docs</a>'
                '<script src="/ReasBook/static/app.js"></script>',
                encoding="utf-8",
            )
            (site / "static" / "app.js").write_text(
                'window.siteRoot = "/ReasBook/";', encoding="utf-8"
            )
            prefix = "/workspace/proxy/3000"

            with running_server(site, prefix) as origin:
                connection = HTTPConnection(
                    "127.0.0.1", int(origin.rsplit(":", 1)[1]), timeout=5
                )
                connection.request("HEAD", "/")
                head = connection.getresponse()
                self.assertEqual(head.status, 301)
                self.assertEqual(
                    head.getheader("Location"), prefix + "/ReasBook/"
                )
                connection.close()

                with urlopen(origin + "/", timeout=5) as response:
                    self.assertEqual(
                        response.geturl(), origin + prefix + "/ReasBook/"
                    )
                    body = response.read().decode()
                self.assertIn(prefix + "/ReasBook/papers/demo/", body)
                self.assertIn(prefix + "/ReasBook/static/app.js", body)
                self.assertIn("../../docs/ReasBook/Demo.html", body)

                with urlopen(
                    origin + prefix + "/ReasBook/static/app.js", timeout=5
                ) as response:
                    script = response.read().decode()
                self.assertIn(prefix + "/ReasBook/", script)

    def test_public_prefix_rejects_urls_and_path_traversal(self) -> None:
        for value in (
            "https://example.test/proxy",
            "/proxy/../secret",
            "/proxy//nested",
            "/proxy?target=other",
        ):
            with self.subTest(value=value), self.assertRaises(ValueError):
                preview._normalize_public_prefix(value)

    def test_ready_file_rejects_target_and_parent_symlinks(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)

            external_file = root / "external-ready.json"
            external_file.write_text("preserve file", encoding="utf-8")
            ready_link = root / "ready-link.json"
            ready_link.symlink_to(external_file)
            with self.assertRaisesRegex(ValueError, "symbolic-link component"):
                preview._safe_ready_file_path(ready_link)
            self.assertTrue(ready_link.is_symlink())
            self.assertEqual(
                external_file.read_text(encoding="utf-8"),
                "preserve file",
            )

            external_parent = root / "external-parent"
            external_parent.mkdir()
            sentinel = external_parent / "sentinel.txt"
            sentinel.write_text("preserve parent", encoding="utf-8")
            parent_link = root / "ready-parent-link"
            parent_link.symlink_to(external_parent, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "symbolic-link component"):
                preview._safe_ready_file_path(parent_link / "ready.json")
            self.assertTrue(parent_link.is_symlink())
            self.assertEqual(
                sentinel.read_text(encoding="utf-8"),
                "preserve parent",
            )
            self.assertFalse((external_parent / "ready.json").exists())


if __name__ == "__main__":
    unittest.main()
