#!/usr/bin/env python3
"""ReasBook multi-book review service.

The service is deliberately useful before the expensive Lean/doc-generation
pipeline exists.  It serves a small catalog, exposes stable per-book API
routes, and keeps review state in SQLite.  Declaration and dependency payloads
are optional per-book artifacts loaded only when a later build creates them.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import sys
from time import monotonic
from typing import Any
from urllib.parse import parse_qsl, unquote, urlencode, urlsplit, urlunsplit

from fastapi import FastAPI, HTTPException, Request, status
from fastapi.responses import FileResponse, HTMLResponse, JSONResponse, PlainTextResponse, RedirectResponse, Response
from starlette.middleware.gzip import GZipMiddleware

from artifacts import EvidenceResolver, GRAPH_ASSETS, rewrite_html_for_proxy
from storage import Actor, ReviewConflict, ReviewStore
from settings import cache_root, data_root

PROJECT_ROOT = Path(__file__).resolve().parent
DATA_ROOT = data_root()
CATALOG_PATH = Path(os.environ.get("REASBOOK_REVIEWER_CATALOG", DATA_ROOT / "catalog.json")).expanduser()
BOOK_DATA_ROOT = Path(os.environ.get("REASBOOK_REVIEWER_BOOK_DATA", DATA_ROOT / "books")).expanduser()
DB_PATH = Path(
    os.environ.get(
        "REASBOOK_REVIEWER_DB",
        cache_root() / "reviewer" / "state" / "reviews.sqlite3",
    )
).expanduser()
DOCS_ROOT = PROJECT_ROOT / "docs"
GRAPHVIZ_RUNTIME = GRAPH_ASSETS / "vendor" / "viz-global.js"
AUTH_SRC_ROOT = Path(
    os.environ.get(
        "REASLAB_AUTH_ROOT",
        PROJECT_ROOT.parents[2] / "reaslab-auth" / "python" / "src",
    )
).expanduser()
STATIC_HEADERS = {"Cache-Control": "no-cache"}

SLUG_RE = re.compile(r"^[a-z0-9][a-z0-9_-]{0,120}$")
ITEM_KEY_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.:-]{0,180}$")
MAX_BODY_BYTES = 128 * 1024
ARTIFACT_NAMES = ("index", "source", "docs", "graphs")
PUBLIC_ARTIFACTS = os.environ.get("REASBOOK_PUBLIC_ARTIFACTS", "true").strip().lower() in {"1", "true", "yes"}
STATIC_ASSETS = {
    "app.js": DOCS_ROOT / "app.js",
    "styles.css": DOCS_ROOT / "styles.css",
    "mathjax-config.js": DOCS_ROOT / "mathjax-config.js",
}
STATIC_FONTS = {
    "ibm-plex-sans-latin.woff2": DOCS_ROOT / "fonts" / "ibm-plex-sans-latin.woff2",
    "ibm-plex-mono-regular-latin.woff2": DOCS_ROOT / "fonts" / "ibm-plex-mono-regular-latin.woff2",
    "ibm-plex-mono-medium-latin.woff2": DOCS_ROOT / "fonts" / "ibm-plex-mono-medium-latin.woff2",
}


def _json_response(payload: Any, status_code: int = 200) -> JSONResponse:
    return JSONResponse(payload, status_code=status_code, headers={"Cache-Control": "no-store"})


def _read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError, UnicodeDecodeError):
        return None


def _with_discovered_papers(payload: dict[str, Any], reasbook_root: Path) -> dict[str, Any]:
    """Add source-truth paper records without replacing cached book metadata."""

    from catalog import discover_books

    existing = {str(entry.get("slug") or "") for entry in payload.get("books", [])}
    papers = [
        record.as_dict()
        for record in discover_books(reasbook_root, include_papers=True)
        if record.kind == "paper" and record.slug not in existing
    ]
    return {**payload, "books": [*payload.get("books", []), *papers]}


def _load_catalog() -> dict[str, Any]:
    """Use validated cached inventory, or discover a lightweight in-memory catalog."""
    from catalog import (
        CatalogError, catalog_payload, default_reasbook_root,
        discover_books, discover_stacks_project, load_catalog,
    )

    root = default_reasbook_root()
    if CATALOG_PATH.is_file():
        try:
            return _with_discovered_papers(load_catalog(CATALOG_PATH), root)
        except (CatalogError, OSError, ValueError):
            import logging

            logging.getLogger(__name__).warning("Invalid reviewer catalog; discovering from source: %s", CATALOG_PATH)
    records = discover_books(root, include_papers=True)
    stacks = discover_stacks_project()
    if stacks is not None:
        records.append(stacks)
    return catalog_payload(records, reasbook_root=root)


CATALOG = _load_catalog()
BOOKS_BY_SLUG: dict[str, dict[str, Any]] = {
    str(book["slug"]): book
    for book in CATALOG.get("books", [])
    if isinstance(book, dict) and isinstance(book.get("slug"), str) and SLUG_RE.fullmatch(book["slug"])
}


def _book_or_404(slug: str) -> dict[str, Any]:
    if not SLUG_RE.fullmatch(slug):
        raise HTTPException(status_code=404, detail="book not found")
    book = BOOKS_BY_SLUG.get(slug)
    if book is None:
        raise HTTPException(status_code=404, detail="book not found")
    return book


def _book_data_dir(slug: str) -> Path:
    # ``slug`` has already passed SLUG_RE; resolve once more so a future caller
    # cannot turn this helper into a path traversal primitive.
    root = BOOK_DATA_ROOT.resolve()
    target = (root / slug).resolve()
    if target.parent != root:
        raise HTTPException(status_code=404, detail="book not found")
    return target


def _load_book_index(slug: str) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    """Load an optional per-book index; absent means a valid empty scaffold."""

    book = _book_or_404(slug)
    review_index = book.get("reviewIndex") if isinstance(book.get("reviewIndex"), dict) else {}
    candidates = [_artifact_path(slug, "index")]
    payload = next((value for value in (_read_catalog_candidate(path) for path in candidates) if value is not None), None)
    if not isinstance(payload, dict):
        state = str(review_index.get("state") or "not-built")
        return {"state": state, "generatedAt": None, "itemCount": 0}, []

    raw_items = payload.get("items", [])
    items: list[dict[str, Any]] = []
    if isinstance(raw_items, list):
        for raw in raw_items:
            if not isinstance(raw, dict):
                continue
            key = raw.get("key", raw.get("id"))
            if not isinstance(key, str) or not ITEM_KEY_RE.fullmatch(key):
                continue
            item = dict(raw)
            item["key"] = key
            items.append(item)
    meta = {
        "state": str(payload.get("state") or "ready"),
        "generatedAt": payload.get("generatedAt"),
        "itemCount": len(items),
    }
    return meta, items


def _read_catalog_candidate(path: Path) -> Any:
    try:
        if not path.is_file():
            return None
    except OSError:
        return None
    return _read_json(path)


def _artifact_path(slug: str, artifact: str) -> Path:
    if artifact not in ARTIFACT_NAMES:
        raise HTTPException(status_code=404, detail="artifact not found")
    book = _book_or_404(slug)
    specs = book.get("artifacts") if isinstance(book.get("artifacts"), dict) else {}
    spec = specs.get(artifact) if isinstance(specs.get(artifact), dict) else {}
    configured = spec.get("path")
    root = _book_data_dir(slug)
    fallback = (root / f"{artifact}.json").resolve()
    if fallback.parent != root:
        raise HTTPException(status_code=404, detail="artifact not found")
    if isinstance(configured, str) and configured:
        # Catalogs are portable: their generated paths traditionally start at
        # ``data/`` while an operator may place DATA_ROOT on another volume.
        # Resolve relative paths against that volume first, then retain support
        # for catalogs authored relative to the application checkout.  Every
        # candidate is constrained to this book's directory below.
        raw = Path(configured).expanduser()
        if raw.is_absolute():
            candidates = [raw]
        else:
            candidates = []
            # The checked-in catalog uses paths rooted at ``data/``.  Strip
            # that presentation prefix when DATA_ROOT has been overridden.
            if raw.parts and raw.parts[0] == "data":
                candidates.append(DATA_ROOT.resolve() / Path(*raw.parts[1:]))
            candidates.extend(
                [
                    DATA_ROOT.resolve().parent / raw,
                    DATA_ROOT.resolve() / raw,
                    PROJECT_ROOT / raw,
                ]
            )
        for candidate_path in candidates:
            candidate = candidate_path.resolve()
            if candidate.parent == root:
                return candidate
    return fallback


def _artifact_status(slug: str, artifact: str) -> dict[str, Any]:
    path = _artifact_path(slug, artifact)
    try:
        exists = path.is_file()
        size = path.stat().st_size if exists else 0
    except OSError:
        exists = False
        size = 0
    book = _book_or_404(slug)
    specs = book.get("artifacts") if isinstance(book.get("artifacts"), dict) else {}
    spec = specs.get(artifact) if isinstance(specs.get(artifact), dict) else {}
    state = str(spec.get("state") or "not-built")
    if exists:
        state = "ready"
        if artifact == "source":
            manifest = _read_json(path)
            if isinstance(manifest, dict) and manifest.get("contentAvailable") is False:
                state = "partial"
    return {
        "name": artifact,
        "state": state,
        "path": str(spec.get("path") or f"data/books/{slug}/{artifact}.json"),
        "sizeBytes": size,
    }


STORE = ReviewStore(DB_PATH)


# Import the sibling identity package only when OAuth configuration is complete.
# This keeps the catalog/read-only scaffold runnable on a fresh checkout while
# ensuring production login always goes through reaslab-auth.
AUTH = None
AUTH_IMPORT_ERROR = ""
AUTH_CONFIGURED = False
AUTH_ENV_NAMES = (
    "REASLAB_OAUTH_ISSUER",
    "REASLAB_OAUTH_CLIENT_ID",
    "REASLAB_OAUTH_CLIENT_SECRET",
    "REASLAB_OAUTH_REDIRECT_URI",
)
ADMIN_SUBJECTS = {
    value.strip()
    for value in os.environ.get("REASBOOK_ADMIN_SUBJECTS", "").split(",")
    if value.strip()
}


async def _remember_authenticated(session: Any) -> None:
    subject = str(session.subject)
    name = str(session.name or "Reader")[:120]
    role = "admin" if subject in ADMIN_SUBJECTS else "reviewer"
    STORE.upsert_user(Actor(subject=subject, display_name=name, email=session.email, role=role))


def _initialize_auth() -> None:
    global AUTH, AUTH_IMPORT_ERROR, AUTH_CONFIGURED
    missing = [name for name in AUTH_ENV_NAMES if not os.environ.get(name, "").strip()]
    if missing:
        AUTH_IMPORT_ERROR = "OAuth is not configured; missing " + ", ".join(missing)
        return
    try:
        if str(AUTH_SRC_ROOT) not in sys.path:
            sys.path.insert(0, str(AUTH_SRC_ROOT))
        from reaslab_auth import ReasLabBffClient, ReasLabBffConfig, ReasLabOAuthClientConfig
        from reaslab_auth.fastapi import ReasLabFastAPIAuth, ReasLabFastAPIConfig

        bff = ReasLabBffClient(
            ReasLabBffConfig(
                oauth=ReasLabOAuthClientConfig(
                    issuer=os.environ["REASLAB_OAUTH_ISSUER"],
                    client_id=os.environ["REASLAB_OAUTH_CLIENT_ID"],
                    client_secret=os.environ["REASLAB_OAUTH_CLIENT_SECRET"],
                    redirect_uri=os.environ["REASLAB_OAUTH_REDIRECT_URI"],
                ),
                session_secret=os.environ.get("REASBOOK_SESSION_SECRET") or None,
            )
        )
        secure = os.environ.get("REASBOOK_SECURE_COOKIES", "true").strip().lower() not in {"0", "false", "no"}
        AUTH = ReasLabFastAPIAuth(
            bff,
            ReasLabFastAPIConfig(
                route_prefix="/api/auth",
                app_base_url=os.environ.get("REASBOOK_APP_BASE_URL", ""),
                session_cookie_name=os.environ.get("REASBOOK_SESSION_COOKIE", "reasbook_session"),
                transaction_cookie_name=os.environ.get("REASBOOK_TRANSACTION_COOKIE", "reasbook_oauth_transaction"),
                secure_cookies=secure,
            ),
            on_authenticated=_remember_authenticated,
        )
        AUTH_CONFIGURED = True
    except Exception as exc:  # ImportError and invalid config are surfaced in health API.
        AUTH_IMPORT_ERROR = f"reaslab-auth could not be initialized: {exc}"


_initialize_auth()


class ReasBookPrefixMiddleware:
    """Expose the reviewer below the published site's familiar URL prefix.

    Siflow's short preview route only forwards requests that remain below
    ``/ReasBook/``. Rewriting the ASGI path keeps the canonical application
    routes single-sourced while the browser-visible prefix stays intact for
    relative assets, navigation, and frontend API requests.
    """

    prefix = "/ReasBook"

    def __init__(self, app: Any) -> None:
        self.app = app

    async def __call__(self, scope: dict[str, Any], receive: Any, send: Any) -> None:
        if scope.get("type") not in {"http", "websocket"}:
            await self.app(scope, receive, send)
            return
        path = str(scope.get("path") or "")
        if path == self.prefix:
            response = RedirectResponse("./ReasBook/", status_code=307)
            await response(scope, receive, send)
            return
        if not path.startswith(f"{self.prefix}/"):
            await self.app(scope, receive, send)
            return

        rewritten = dict(scope)
        rewritten["path"] = path[len(self.prefix) :] or "/"
        raw_path = scope.get("raw_path")
        raw_prefix = self.prefix.encode("ascii")
        if isinstance(raw_path, bytes) and raw_path.startswith(raw_prefix):
            rewritten["raw_path"] = raw_path[len(raw_prefix) :] or b"/"
        rewritten["root_path"] = f"{scope.get('root_path', '').rstrip('/')}{self.prefix}"
        await self.app(rewritten, receive, send)


app = FastAPI(title="ReasBook Reviewer", docs_url=None, redoc_url=None)
app.add_middleware(GZipMiddleware, minimum_size=1024)
app.add_middleware(ReasBookPrefixMiddleware)
if AUTH is not None:
    app.include_router(AUTH.router)


def _rewrite_auth_cookie_paths(response: Any) -> None:
    """Keep the transaction cookie usable when an ingress adds a path prefix.

    reaslab-auth correctly scopes its transaction cookie to ``/api/auth/oauth``
    when served at the root.  A path-stripping reverse proxy exposes that route
    below an external prefix, so the browser would otherwise never send the
    cookie back.  The cookie name is service-specific and short-lived; widening
    its path to ``/`` also lets the callback/error response reliably clear it.
    """

    cookie_path = os.environ.get("REASBOOK_AUTH_COOKIE_PATH", "/")
    if not cookie_path.startswith("/") or any(char in cookie_path for char in ";\r\n"):
        raise ValueError("REASBOOK_AUTH_COOKIE_PATH must be an absolute cookie path")
    rewritten = []
    for name, value in response.raw_headers:
        if name.lower() == b"set-cookie":
            value = value.replace(b"Path=/api/auth/oauth", b"Path=/")
            # Shared-host service gateways must not send auth cookies to sibling services.
            value = re.sub(rb"Path=/(;|$)", lambda match: b"Path=" + cookie_path.encode("ascii") + match[1], value)
        rewritten.append((name, value))
    response.raw_headers = rewritten


def _canonical_auth_return_to(value: str, prefix: str) -> str:
    """Keep gateway aliases inside the path that owns the session cookie."""
    parsed = urlsplit(value)
    decoded = unquote(parsed.path)
    if (not value.startswith("/") or value.startswith("//") or parsed.netloc
            or parsed.scheme or "\\" in decoded or any(part in {".", ".."} for part in decoded.split("/"))):
        return prefix
    if "/ReasBook/" in parsed.path:
        suffix = parsed.path.split("/ReasBook/", 1)[1]
    elif parsed.path.startswith("/books/"):
        suffix = parsed.path.lstrip("/")
    else:
        suffix = ""
    return urlunsplit(("", "", prefix + suffix, parsed.query, parsed.fragment))


@app.middleware("http")
async def security_headers(request: Request, call_next):
    prefix = os.environ.get("REASBOOK_AUTH_COOKIE_PATH", "/")
    if prefix != "/" and request.url.path.endswith("/api/auth/oauth/start"):
        # SiFlow exposes hash and human-readable aliases. The callback is on
        # the registered hash route; returning to another alias loses cookies.
        params = parse_qsl(request.scope.get("query_string", b"").decode("ascii"), keep_blank_values=True)
        target = next((value for key, value in params if key == "return_to"), "/")
        params = [(key, value) for key, value in params if key != "return_to"]
        params.append(("return_to", _canonical_auth_return_to(target, prefix)))
        request.scope["query_string"] = urlencode(params).encode("ascii")
    response = await call_next(request)
    _rewrite_auth_cookie_paths(response)
    response.headers.setdefault("X-Content-Type-Options", "nosniff")
    response.headers.setdefault("X-Frame-Options", "SAMEORIGIN")
    response.headers.setdefault("Referrer-Policy", "same-origin")
    response.headers.setdefault(
        "Content-Security-Policy",
        "default-src 'self'; script-src 'self' https://cdn.jsdelivr.net; "
        "style-src 'self' 'unsafe-inline' https://cdn.jsdelivr.net; "
        "font-src 'self' https://cdn.jsdelivr.net data:; "
        "connect-src 'self' https://cdn.jsdelivr.net; frame-ancestors 'self'",
    )
    return response


if AUTH is None:
    async def _auth_unavailable() -> JSONResponse:
        return _json_response(
            {"error": "ReasLab authentication is not configured", "detail": AUTH_IMPORT_ERROR or "authentication unavailable"},
            status.HTTP_503_SERVICE_UNAVAILABLE,
        )

    @app.get("/api/auth/oauth/start")
    async def auth_start_unavailable() -> JSONResponse:
        return await _auth_unavailable()

    @app.get("/api/auth/oauth/callback")
    async def auth_callback_unavailable() -> JSONResponse:
        return await _auth_unavailable()

    @app.get("/api/auth/csrf")
    async def auth_csrf_unavailable() -> JSONResponse:
        return await _auth_unavailable()

    @app.post("/api/auth/logout")
    async def auth_logout_unavailable() -> JSONResponse:
        return await _auth_unavailable()


@app.get("/", include_in_schema=False)
async def index() -> FileResponse:
    return FileResponse(DOCS_ROOT / "index.html", media_type="text/html", headers=STATIC_HEADERS)


@app.get("/books/{slug}", include_in_schema=False)
async def book_without_slash(slug: str) -> RedirectResponse:
    _book_or_404(slug)
    # A relative redirect preserves an external path prefix added by an ingress.
    return RedirectResponse(f"./{slug}/", status_code=307)


@app.get("/books/{slug}/", include_in_schema=False)
async def book_page(slug: str) -> FileResponse:
    _book_or_404(slug)
    return FileResponse(DOCS_ROOT / "index.html", media_type="text/html", headers=STATIC_HEADERS)


@app.get("/books/{slug}/assets/{asset_name}", include_in_schema=False)
async def book_static_asset(slug: str, asset_name: str) -> FileResponse:
    _book_or_404(slug)
    return await static_asset(asset_name)


@app.get("/books/{slug}/assets/fonts/{font_name}", include_in_schema=False)
async def book_static_font(slug: str, font_name: str) -> FileResponse:
    _book_or_404(slug)
    return await static_font(font_name)


@app.get("/api/health")
async def health() -> JSONResponse:
    ready_indexes = sum(
        1
        for book in BOOKS_BY_SLUG.values()
        if _artifact_status(str(book["slug"]), "index")["state"] == "ready"
    )
    return _json_response(
        {
            "ok": True,
            "service": "reasbook-reviewer",
            "catalogBooks": len(BOOKS_BY_SLUG),
            "cachePolicy": CATALOG.get("cachePolicy", {"mode": "on-demand", "generated": False}),
            "cacheGenerated": ready_indexes > 0,
            "readyBookIndexes": ready_indexes,
            "auth": {
                "provider": "reaslab",
                "configured": AUTH_CONFIGURED,
                "error": AUTH_IMPORT_ERROR or None,
            },
            "database": "sqlite",
        }
    )


@app.get("/api/catalog")
async def catalog() -> JSONResponse:
    payload = dict(CATALOG)
    payload["books"] = [_book_entry_with_runtime_artifacts(book) for book in BOOKS_BY_SLUG.values()]
    return _json_response(payload)


def _book_entry_with_runtime_artifacts(book: dict[str, Any]) -> dict[str, Any]:
    entry = dict(book)
    artifacts = {name: _artifact_status(str(book["slug"]), name) for name in ARTIFACT_NAMES}
    entry["artifacts"] = artifacts
    review_index = dict(book.get("reviewIndex")) if isinstance(book.get("reviewIndex"), dict) else {}
    review_index["state"] = artifacts["index"]["state"]
    graph = _resolver_for(str(book["slug"])).graph_payload()
    graph_items = graph.get("items") if isinstance(graph, dict) else None
    if isinstance(graph_items, list):
        review_index["itemCount"] = len(graph_items)
        review_index["reviewUnit"] = "book-statement"
    entry["reviewIndex"] = review_index
    return entry


def _resolver_for(slug: str) -> EvidenceResolver:
    """Reuse evidence briefly, but notice atomic index publication immediately."""
    book = _book_or_404(slug)
    index_path = _artifact_path(slug, "index")
    try:
        info = index_path.stat()
        identity = (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)
    except OSError:
        identity = None
    signature = (index_path, identity)
    now = monotonic()
    cached = RESOURCE_RESOLVERS.get(slug)
    if cached is None or cached.index_signature != signature or now >= cached.expires_at:
        resolver = EvidenceResolver(book, project_root=PROJECT_ROOT, data_root=DATA_ROOT, index_path=index_path)
        cached = _ResolverCacheEntry(resolver, signature, now + RESOURCE_RESOLVER_TTL_SECONDS)
        RESOURCE_RESOLVERS[slug] = cached
    return cached.resolver


@dataclass(frozen=True)
class _ResolverCacheEntry:
    resolver: EvidenceResolver
    index_signature: tuple[Path, tuple[int, ...] | None]
    expires_at: float


RESOURCE_RESOLVER_TTL_SECONDS = 60.0
RESOURCE_RESOLVERS: dict[str, _ResolverCacheEntry] = {}


def _fallback_item_key(slug: str, graph_item: dict[str, Any]) -> str:
    source = str(graph_item.get("file") or "").replace("/", ".").removesuffix(".lean")
    declaration = str(graph_item.get("declaration") or graph_item.get("id") or "statement")
    base = re.sub(r"[^A-Za-z0-9_.:-]+", "_", f"{slug}.{source}.{declaration}").strip("._-")
    if len(base) <= 180:
        return base
    digest = hashlib.sha1(base.encode("utf-8")).hexdigest()[:12]
    return f"{base[:167]}_{digest}"


def _review_items(slug: str) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    cache, raw_items = _load_book_index(slug)
    graph = _resolver_for(slug).graph_payload()
    graph_items = graph.get("items") if isinstance(graph, dict) and isinstance(graph.get("items"), list) else []
    if not graph_items:
        return cache, raw_items
    by_source_name = {
        (str(item.get("sourcePath") or ""), str(item.get("name") or "")): item
        for item in raw_items
    }
    result: list[dict[str, Any]] = []
    matched_raw_keys: set[str] = set()
    for graph_item in graph_items:
        if not isinstance(graph_item, dict):
            continue
        source_path = str(graph_item.get("file") or "")
        declaration = str(graph_item.get("declaration") or "")
        raw = by_source_name.get((source_path, declaration), {})
        if raw:
            matched_raw_keys.add(str(raw.get("key") or ""))
        item = dict(raw)
        item.update(
            {
                "key": str(raw.get("key") or _fallback_item_key(slug, graph_item)),
                "kind": str(graph_item.get("type") or raw.get("kind") or "statement").lower(),
                "name": declaration or str(raw.get("name") or "statement"),
                "title": str(graph_item.get("title") or raw.get("title") or declaration),
                "statement": str(graph_item.get("statement") or ""),
                "label": str(graph_item.get("label") or ""),
                "section": str(graph_item.get("section") or ""),
                "sourcePath": source_path or str(raw.get("sourcePath") or ""),
                "line": int(raw.get("line") or graph_item.get("line") or 0),
                "graphId": str(graph_item.get("id") or ""),
                "dependencies": graph_item.get("dependencies") if isinstance(graph_item.get("dependencies"), list) else [],
            }
        )
        result.append(item)
    # Keep source-index items whose source/declaration metadata predates the
    # graph. This preserves stable review URLs while still exposing graph-only
    # projects that have no lightweight index at all.
    result.extend(
        item for item in raw_items
        if str(item.get("key") or "") not in matched_raw_keys
    )
    cache = {**cache, "itemCount": len(result), "reviewUnit": "book-statement"}
    return cache, result


def _item_for(slug: str, item_key: str) -> dict[str, Any]:
    _book_or_404(slug)
    if not ITEM_KEY_RE.fullmatch(item_key):
        raise HTTPException(status_code=400, detail="invalid item key")
    _cache, items = _review_items(slug)
    item = next((value for value in items if str(value.get("key")) == item_key), None)
    if item is None:
        raise HTTPException(status_code=404, detail="review item not found")
    return item


def _source_snapshot(resolver: EvidenceResolver, item: dict[str, Any]) -> dict[str, Any]:
    source_path = str(item.get("sourcePath") or "")
    line_number = max(1, int(item.get("line") or 1))
    path = resolver.source_path(source_path)
    if path is None:
        return {
            "available": False,
            "path": source_path,
            "line": line_number,
            "start": line_number,
            "end": line_number,
            "lines": [],
        }
    try:
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return {"available": False, "path": source_path, "line": line_number, "start": line_number, "end": line_number, "lines": []}
    start = max(1, line_number - 18)
    end = min(len(lines), line_number + 28)
    return {
        "available": True,
        "path": source_path,
        "line": line_number,
        "start": start,
        "end": end,
        "totalLines": len(lines),
        "lines": [
            {"number": number, "text": lines[number - 1], "target": number == line_number}
            for number in range(start, end + 1)
        ],
    }


@app.get("/api/books")
async def books() -> JSONResponse:
    entries = [_book_entry_with_runtime_artifacts(book) for book in BOOKS_BY_SLUG.values()]
    return _json_response({"books": entries, "count": len(entries)})


@app.get("/api/books/{slug}")
async def book_detail(slug: str) -> JSONResponse:
    book = _book_or_404(slug)
    cache, items = _review_items(slug)
    entry = _book_entry_with_runtime_artifacts(book)
    return _json_response(
        {
            **entry,
            "cache": cache,
            "items": items,
        }
    )


@app.get("/api/books/{slug}/index")
async def book_index(slug: str) -> JSONResponse:
    _book_or_404(slug)
    cache, items = _review_items(slug)
    return _json_response({"bookSlug": slug, "cache": cache, "items": items})


@app.get("/api/books/{slug}/resources")
async def book_resources(slug: str) -> JSONResponse:
    """Return read-only source, docs, Verso, and graph capabilities for a book."""

    _book_or_404(slug)
    resolver = _resolver_for(slug)
    return _json_response(
        {
            "bookSlug": slug,
            "resources": resolver.manifest(f"/api/books/{slug}"),
        }
    )


@app.get("/api/books/{slug}/context/{item_key:path}")
async def book_item_context(slug: str, item_key: str, request: Request) -> JSONResponse:
    """Resolve one review item into all available evidence surfaces."""

    _require_evidence_access(request)
    item = _item_for(slug, item_key)
    resolver = _resolver_for(slug)
    resources = resolver.manifest(f"/api/books/{slug}", item)
    return _json_response(
        {
            "bookSlug": slug,
            "item": item,
            "resources": resources,
            "source": _source_snapshot(resolver, item),
            "lean": resolver.lean_contract(item),
            "graph": resolver.graph_for_item(item),
        }
    )


@app.get("/api/books/{slug}/graph")
async def book_graph(slug: str, request: Request) -> JSONResponse:
    _require_evidence_access(request)
    resolver = _resolver_for(slug)
    payload = resolver.graph_payload()
    if payload is None:
        return _json_response(
            {
                "bookSlug": slug,
                "available": False,
                "items": [],
                "edges": [],
            }
        )
    return _json_response({"bookSlug": slug, "available": True, **payload})


@app.get("/api/books/{slug}/artifacts")
async def book_artifacts(slug: str) -> JSONResponse:
    _book_or_404(slug)
    return _json_response(
        {"bookSlug": slug, "artifacts": {name: _artifact_status(slug, name) for name in ARTIFACT_NAMES}}
    )


@app.get("/api/books/{slug}/artifacts/{artifact}")
async def book_artifact(slug: str, artifact: str, request: Request) -> JSONResponse:
    if artifact != "index":
        _require_evidence_access(request)
    path = _artifact_path(slug, artifact)
    if not path.is_file():
        resolver = _resolver_for(slug)
        if artifact == "graphs" and resolver.graph_payload() is not None:
            return _json_response(resolver.graph_payload())
        if artifact in {"docs", "source"} and resolver.resolve() is not None:
            return _json_response(resolver.manifest(f"/api/books/{slug}"))
        raise HTTPException(
            status_code=404,
            detail={"code": "artifact_not_built", "artifact": artifact, "status": _artifact_status(slug, artifact)},
        )
    payload = _read_json(path)
    if payload is None:
        raise HTTPException(status_code=500, detail="artifact is not valid JSON")
    return _json_response(payload)


@app.get("/api/books/{slug}/evidence/{kind}/{path:path}", include_in_schema=False, response_model=None)
async def book_evidence_file(slug: str, kind: str, path: str, request: Request) -> Response:
    """Serve one docs or Verso file through a path-constrained read-only proxy."""

    _require_evidence_access(request)
    _book_or_404(slug)
    if kind not in {"docs", "documentation", "verso", "graph"}:
        raise HTTPException(status_code=404, detail="evidence surface not found")
    if not path:
        path = "index.html"
    if kind == "graph" and path == "vendor/viz-global.js":
        if not GRAPHVIZ_RUNTIME.is_file():
            raise HTTPException(status_code=404, detail="Graphviz runtime not found")
        return FileResponse(
            GRAPHVIZ_RUNTIME,
            media_type="text/javascript",
            headers=STATIC_HEADERS,
        )
    resolver = _resolver_for(slug)
    if kind == "graph" and path == "data.json":
        # Legacy curated releases embed ITEMS in app.js. The resolver validates
        # its JSON-only literal, endpoints/counts and release identity without
        # evaluating JS; expose that same read-only payload to the shared UI.
        payload = resolver.graph_payload()
        if payload and (payload.get("generation") or {}).get("mode") in {"curated", "curated-static"}:
            return _json_response(payload)
    resolved = resolver.evidence_file(kind, path)
    if resolved is None:
        raise HTTPException(status_code=404, detail="evidence file not found")
    file_path, evidence = resolved
    if file_path.suffix.lower() in {".html", ".htm"}:
        try:
            text = file_path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            raise HTTPException(status_code=404, detail="evidence file not found") from None
        prefix = f"/api/books/{slug}/evidence/{kind}"
        # Verso's own navigation script canonicalizes any URL containing a
        # `/docs/` segment back into its site-root route. Use the
        # documentation alias here so statement links survive that rewrite;
        # both aliases resolve to the same read-only docs tree.
        docs_prefix = f"/api/books/{slug}/evidence/documentation" if kind == "verso" else ""
        relative_base = ""
        if kind == "verso":
            relative_path = file_path.relative_to(evidence.site_root)
            depth = len(relative_path.parent.parts)
            relative_base = "../" * depth if depth else "./"
        text = rewrite_html_for_proxy(
            text,
            kind=kind,
            prefix=prefix,
            branch=evidence.branch,
            docs_prefix=docs_prefix,
            relative_base=relative_base,
            project_id=evidence.project_id,
            project_kind=evidence.project_kind,
        )
        script_sources = "'self' 'unsafe-inline' https:"
        if kind == "graph":
            # The vendored Viz.js runtime used by the reference TR_LALM map
            # instantiates its local Graphviz WebAssembly module through an
            # Emscripten loader. Chromium versions in our embedded preview
            # require unsafe-eval in addition to wasm-unsafe-eval for that
            # trusted, same-origin runtime. Keep the exception scoped to the
            # read-only graph surface; Docs and Verso retain the tighter CSP.
            script_sources = (
                "'self' 'unsafe-inline' 'unsafe-eval' 'wasm-unsafe-eval' https:"
            )
        return HTMLResponse(
            text,
            headers={
                **STATIC_HEADERS,
                "Content-Security-Policy": (
                    "default-src 'self' https: data:; "
                    f"script-src {script_sources}; "
                    "style-src 'self' 'unsafe-inline' https:; img-src 'self' https: data:; "
                    "font-src 'self' https: data:; connect-src 'self' https:; frame-ancestors 'self'"
                ),
            },
        )
    media_type = None
    suffix = file_path.suffix.lower()
    if suffix == ".css":
        media_type = "text/css"
    elif suffix == ".js":
        media_type = "text/javascript"
    elif suffix == ".svg":
        media_type = "image/svg+xml"
    return FileResponse(file_path, media_type=media_type, headers=STATIC_HEADERS)


def _parse_since(request: Request) -> int | None:
    value = request.query_params.get("since")
    if value is None or value == "":
        return None
    try:
        return max(0, int(value))
    except ValueError:
        raise HTTPException(status_code=400, detail="invalid since") from None


@app.get("/api/books/{slug}/reviews")
async def list_book_reviews(slug: str, request: Request) -> JSONResponse:
    _book_or_404(slug)
    return _json_response(STORE.list_reviews(slug, _parse_since(request)))


@app.get("/api/books/{slug}/reviews/{item_key}/history")
async def review_history(slug: str, item_key: str) -> JSONResponse:
    _book_or_404(slug)
    if not ITEM_KEY_RE.fullmatch(item_key):
        raise HTTPException(status_code=400, detail="invalid item key")
    return _json_response({"bookSlug": slug, "itemKey": item_key, "events": STORE.list_history(slug, item_key)})


def _session_for(request: Request) -> Any | None:
    if AUTH is None:
        return None
    return AUTH.get_session(request)


def _require_evidence_access(request: Request) -> None:
    if PUBLIC_ARTIFACTS:
        return
    if AUTH is None:
        raise HTTPException(status_code=503, detail="ReasLab authentication is unavailable")
    if _session_for(request) is None:
        raise HTTPException(status_code=401, detail="ReasLab authentication required")


def _actor_for(request: Request) -> Actor:
    if AUTH is None:
        detail = AUTH_IMPORT_ERROR or "ReasLab authentication is unavailable"
        raise HTTPException(status_code=503, detail=detail)
    session = _session_for(request)
    if session is None:
        raise HTTPException(status_code=401, detail="ReasLab authentication required")
    subject = str(session.subject)
    display_name = str(session.name or "Reader")[:120]
    role = "admin" if subject in ADMIN_SUBJECTS else STORE.role_for(subject)
    actor = Actor(subject=subject, display_name=display_name, email=session.email, role=role)
    STORE.upsert_user(actor)
    return actor


async def _validate_csrf(request: Request, session: Any) -> None:
    if AUTH is None:
        return
    AUTH.validate_csrf(request, session)


@app.post("/api/books/{slug}/reviews/{item_key}")
async def save_book_review(slug: str, item_key: str, request: Request) -> JSONResponse:
    _book_or_404(slug)
    if not ITEM_KEY_RE.fullmatch(item_key):
        raise HTTPException(status_code=400, detail="invalid item key")
    cache, items = _review_items(slug)
    known_keys = {str(item.get("key")) for item in items}
    if item_key not in known_keys:
        raise HTTPException(
            status_code=409,
            detail={
                "code": "review_index_not_ready",
                "message": "This book has no generated review items yet.",
                "cache": cache,
            },
        )
    actor = _actor_for(request)
    session = _session_for(request)
    await _validate_csrf(request, session)
    try:
        body = bytearray()
        async for chunk in request.stream():
            if len(body) + len(chunk) > MAX_BODY_BYTES:
                raise HTTPException(status_code=413, detail="request body too large")
            body.extend(chunk)
        payload = json.loads(bytes(body) or b"{}")
    except (json.JSONDecodeError, UnicodeDecodeError):
        raise HTTPException(status_code=400, detail="invalid JSON") from None
    try:
        saved = STORE.save_review(
            slug,
            item_key,
            payload,
            actor,
            remote_addr=request.client.host if request.client else "",
            user_agent=request.headers.get("user-agent", ""),
        )
    except ReviewConflict as conflict:
        return _json_response(
            {
                "error": "review conflict",
                "current": conflict.current,
                "message": "This review changed after it was loaded.",
            },
            status.HTTP_409_CONFLICT,
        )
    except ValueError as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from None
    return _json_response({"bookSlug": slug, "review": saved})


@app.get("/api/session")
async def session_info(request: Request) -> JSONResponse:
    session = _session_for(request)
    if session is None:
        return _json_response(
            {
                "authMode": "reaslab",
                "authProvider": "reaslab",
                "authConfigured": AUTH_CONFIGURED,
                "authenticated": False,
                "user": None,
                "canSave": False,
                "canExport": False,
                "canLogin": AUTH_CONFIGURED,
                "canLogout": False,
            }
        )
    subject = str(session.subject)
    display_name = str(session.name or "Reader")[:120]
    actor = Actor(
        subject=subject,
        display_name=display_name,
        email=session.email,
        role="admin" if subject in ADMIN_SUBJECTS else STORE.role_for(subject),
    )
    STORE.upsert_user(actor)
    return _json_response(
        {
            "authMode": "reaslab",
            "authProvider": "reaslab",
            "authConfigured": AUTH_CONFIGURED,
            "authenticated": True,
            "user": {
                "id": subject,
                "displayName": display_name,
                "email": session.email,
                "role": actor.role,
                "authMethod": "reaslab-oauth",
            },
            "canSave": True,
            "canExport": actor.role == "admin",
            "canLogin": False,
            "canLogout": True,
        }
    )


@app.get("/api/auth/status")
async def auth_status() -> JSONResponse:
    return _json_response(
        {
            "provider": "reaslab",
            "configured": AUTH_CONFIGURED,
            "error": AUTH_IMPORT_ERROR or None,
            "routes": {
                "start": "/api/auth/oauth/start",
                "callback": "/api/auth/oauth/callback",
                "csrf": "/api/auth/csrf",
                "logout": "/api/auth/logout",
            },
        }
    )


@app.get("/api/reviews/export.jsonl")
async def export_reviews(request: Request) -> PlainTextResponse:
    actor = _actor_for(request)
    if actor.role != "admin":
        raise HTTPException(status_code=403, detail="admin role required")
    return _export_events_response(STORE.list_events())


@app.get("/api/books/{slug}/reviews/export.jsonl")
async def export_book_reviews(slug: str, request: Request) -> PlainTextResponse:
    _book_or_404(slug)
    actor = _actor_for(request)
    if actor.role != "admin":
        raise HTTPException(status_code=403, detail="admin role required")
    return _export_events_response(STORE.list_events(slug))


def _export_events_response(events: list[dict[str, Any]]) -> PlainTextResponse:
    body = "".join(json.dumps(event, ensure_ascii=False) + "\n" for event in events)
    return PlainTextResponse(
        content=body,
        media_type="application/x-ndjson",
        headers={"Cache-Control": "no-store", "Content-Disposition": "attachment; filename=review-events.jsonl"},
    )


@app.get("/assets/{asset_name}", include_in_schema=False)
async def static_asset(asset_name: str) -> FileResponse:
    path = STATIC_ASSETS.get(asset_name)
    if path is None:
        raise HTTPException(status_code=404, detail="asset not found")
    return FileResponse(path, headers=STATIC_HEADERS)


@app.get("/assets/fonts/{font_name}", include_in_schema=False)
async def static_font(font_name: str) -> FileResponse:
    path = STATIC_FONTS.get(font_name)
    if path is None:
        raise HTTPException(status_code=404, detail="font not found")
    return FileResponse(path, media_type="font/woff2", headers={"Cache-Control": "public, max-age=31536000, immutable"})


if __name__ == "__main__":
    import uvicorn

    uvicorn.run(
        app,
        host=os.environ.get("REASBOOK_REVIEWER_HOST", "127.0.0.1"),
        port=int(os.environ.get("REASBOOK_REVIEWER_PORT", "8876")),
    )
