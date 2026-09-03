"""Deterministic target artifacts derived from one verified release site."""

from __future__ import annotations

from dataclasses import replace
import hashlib
import html
from html.parser import HTMLParser
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
from urllib.parse import unquote, urljoin, urlsplit
import uuid

from reasbook_sdk_common import atomic_write_json

from ..errors import DeployExecutionError
from ..git import version_key
from .models import ReleaseArtifactPolicy, ReleaseSpec
from .results import (
    BundleInfo,
    ReleaseArtifactRecord,
    ReleaseManifest,
    ReleaseSetManifest,
)
from .store import ReleaseLayout, ReleaseStore


_SHARED_DOC_DIRECTORIES = {"declarations", "find", "src"}


class _ReferenceParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.base_href: str | None = None
        self.references: list[tuple[str, str, str]] = []

    def handle_starttag(
        self,
        tag: str,
        attrs: list[tuple[str, str | None]],
    ) -> None:
        values = dict(attrs)
        if tag == "base":
            if self.base_href is None and values.get("href"):
                self.base_href = values["href"]
            return
        if (
            tag == "meta"
            and (values.get("http-equiv") or "").lower() == "refresh"
            and values.get("content")
        ):
            match = re.match(
                r"^\s*\d+(?:\.\d+)?\s*;\s*url\s*=\s*(.*?)\s*$",
                values["content"],
                flags=re.IGNORECASE,
            )
            if match and match.group(1):
                self.references.append(
                    (tag, "refresh", match.group(1).strip("\"'"))
                )
        for attribute in ("href", "src"):
            value = values.get(attribute)
            if value:
                self.references.append((tag, attribute, value))


def artifact_policy_digest(
    policies: tuple[ReleaseArtifactPolicy, ...],
) -> str:
    payload = {
        policy.name: policy.public_dict()
        for policy in sorted(policies, key=lambda item: item.name)
    }
    encoded = json.dumps(
        payload,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


class PagesSiteProjector:
    """Create a bounded Pages view without changing the full release tree.

    Canonical project pages retain their original version-qualified URLs.  Full
    dependency API pages are replaced with explicit lightweight placeholders;
    referenced styles, scripts, images, and search data remain byte-identical.
    """

    def project(
        self,
        spec: ReleaseSpec,
        source: Path,
        destination: Path,
    ) -> Path:
        full_site = Path(source).expanduser().resolve()
        target = Path(destination).expanduser().resolve(strict=False)
        self._validate_site(full_site)
        if (
            full_site == target
            or full_site in target.parents
            or target in full_site.parents
        ):
            raise DeployExecutionError(
                "Pages artifact and full site must be disjoint trees"
            )

        target.parent.mkdir(parents=True, exist_ok=True)
        staged = target.parent / f".pages-site-{uuid.uuid4().hex}"
        backup = target.parent / f".pages-site-backup-{uuid.uuid4().hex}"
        try:
            shutil.copytree(
                full_site,
                staged,
                ignore=self._ignore_top_level_versions(full_site),
            )
            atomic_write_json(staged / "release-spec.json", spec.public_dict())
            versions = staged / "versions"
            versions.mkdir()
            for branch in sorted(
                spec.branches,
                key=lambda item: version_key(item.name),
            ):
                self._project_branch(spec, full_site, versions, branch.name)
            self._copy_if_present(
                full_site,
                staged,
                Path("versions") / "index.html",
            )
            self._close_internal_references(spec, full_site, staged)
            self._validate_required_content(spec, staged)
            self._validate_site(staged)
            self._publish(staged, target, backup)
            return target
        finally:
            if staged.exists():
                shutil.rmtree(staged)
            if backup.exists() or backup.is_symlink():
                if backup.is_dir() and not backup.is_symlink():
                    shutil.rmtree(backup)
                else:
                    backup.unlink(missing_ok=True)

    @staticmethod
    def _ignore_top_level_versions(root: Path):
        def ignore(directory: str, names: list[str]) -> set[str]:
            return {"versions"} if Path(directory).resolve() == root else set()

        return ignore

    def _project_branch(
        self,
        spec: ReleaseSpec,
        full_site: Path,
        versions: Path,
        branch: str,
    ) -> None:
        source = full_site / "versions" / branch
        if not source.is_dir():
            raise DeployExecutionError(
                f"full release is missing version tree required by Pages: {branch}"
            )
        target = versions / branch
        target.mkdir()
        projects = tuple(
            project
            for project in spec.canonical_projects()
            if project.branch == branch
        )

        for relative in (Path("static"), Path("-verso-docs.json")):
            self._copy_if_present(source, target, relative)
        self._copy_doc_runtime(source, target)

        project_routes: list[tuple[str, str]] = []
        for project in projects:
            candidates = (
                Path(project.kind) / project.slug,
                Path(project.slug),
            )
            chosen: Path | None = None
            for relative in candidates:
                if self._copy_if_present(source, target, relative) and chosen is None:
                    chosen = relative
            self._copy_if_present(
                source,
                target,
                Path("theorem-maps") / project.kind / project.slug,
            )
            self._copy_project_docs(source, target, project.kind, project.project_id)
            if chosen is not None:
                project_routes.append(
                    (
                        chosen.as_posix().rstrip("/") + "/",
                        project.project_id,
                    )
                )

        (target / "index.html").write_text(
            self._branch_index(branch, project_routes),
            encoding="utf-8",
        )

    @staticmethod
    def _copy_if_present(source: Path, destination: Path, relative: Path) -> bool:
        item = source / relative
        if item.is_symlink():
            raise DeployExecutionError(f"release site contains a symlink: {item}")
        if item.is_dir():
            target = destination / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copytree(item, target, dirs_exist_ok=True)
            return True
        if item.is_file():
            target = destination / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(item, target)
            return True
        return False

    def _copy_doc_runtime(self, source: Path, destination: Path) -> None:
        docs = source / "docs"
        if not docs.is_dir():
            return
        target_docs = destination / "docs"
        target_docs.mkdir(parents=True, exist_ok=True)
        for child in docs.iterdir():
            if child.is_file():
                self._copy_if_present(source, destination, child.relative_to(source))

        for root_name in ("ReasBook",):
            root = docs / root_name
            if not root.is_dir():
                continue
            target_root = target_docs / root_name
            target_root.mkdir(parents=True, exist_ok=True)
            for child in root.iterdir():
                relative = child.relative_to(source)
                if child.is_file() or child.name in _SHARED_DOC_DIRECTORIES:
                    self._copy_if_present(source, destination, relative)

    def _copy_project_docs(
        self,
        source: Path,
        destination: Path,
        kind: str,
        project_id: str,
    ) -> None:
        kind_title = "Books" if kind == "books" else "Papers"
        candidates = (
            Path("docs") / "ReasBook" / kind_title / project_id,
            Path("docs") / "ReasBook" / project_id,
            Path("docs") / kind_title / project_id,
            Path("docs") / project_id,
            Path("docs") / "ReasBook" / f"{project_id}.html",
            Path("docs") / f"{project_id}.html",
        )
        for relative in candidates:
            self._copy_if_present(source, destination, relative)

    @staticmethod
    def _branch_index(
        branch: str,
        routes: list[tuple[str, str]],
    ) -> str:
        items = "\n".join(
            "      <li><a href=\"{}\"><code>{}</code></a></li>".format(
                html.escape(route, quote=True), html.escape(name)
            )
            for route, name in routes
        )
        if not items:
            items = (
                "      <li>No canonical projects are published for this "
                "version.</li>"
            )
        home = "../../"
        return "\n".join(
            [
                "<!doctype html>",
                '<html lang="en">',
                "<head>",
                '  <meta charset="utf-8" />',
                '  <meta name="viewport" '
                'content="width=device-width,initial-scale=1" />',
                f"  <title>ReasBook {html.escape(branch)}</title>",
                '  <link rel="stylesheet" href="../../static/catalog.css" />',
                "</head>",
                "<body>",
                '  <main class="page-shell narrow-shell">',
                '    <p class="eyebrow">Canonical Pages Projection</p>',
                f"    <h1><span translate=\"no\">{html.escape(branch)}</span></h1>",
            "    <p>API links outside project roots resolve to explicit "
            "dependency placeholders.</p>",
                '    <ul class="resource-list">',
                items,
                "    </ul>",
                f'    <a class="back-link" href="{home}">Back to ReasBook</a>',
                "  </main>",
                "</body>",
                "</html>",
                "",
            ]
        )

    def _close_internal_references(
        self,
        spec: ReleaseSpec,
        full_site: Path,
        pages_site: Path,
    ) -> None:
        origin = "https://reasbook.invalid"
        base_path = spec.base_path
        errors: list[str] = []
        documents = sorted(pages_site.rglob("*.html"))
        for document in documents:
            parser = _ReferenceParser()
            parser.feed(document.read_text(encoding="utf-8", errors="replace"))
            relative_document = document.relative_to(pages_site).as_posix()
            document_url = origin + base_path + relative_document
            document_base = (
                urljoin(document_url, parser.base_href)
                if parser.base_href
                else document_url
            )
            for tag, attribute, value in parser.references:
                missing = self._resolve_missing_reference(
                    origin,
                    base_path,
                    document_base,
                    value,
                    pages_site,
                )
                if missing is None:
                    continue
                relative, target = missing
                source = full_site / relative
                if source.is_file():
                    if source.suffix.lower() in {".html", ".htm"}:
                        if self._is_omitted_dependency_doc(relative):
                            self._write_dependency_stub(target, spec.base_path)
                        else:
                            errors.append(
                                f"{relative_document}: omitted non-dependency page {value}"
                            )
                    else:
                        target.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(source, target)
                elif source.is_dir() and (source / "index.html").is_file():
                    if self._is_omitted_dependency_doc(relative / "index.html"):
                        self._write_dependency_stub(
                            target / "index.html",
                            spec.base_path,
                        )
                    else:
                        errors.append(
                            f"{relative_document}: omitted non-dependency directory {value}"
                        )
                else:
                    errors.append(
                        f"{relative_document}: {tag}.{attribute} target is missing: {value}"
                    )
        if errors:
            preview = "; ".join(errors[:20])
            suffix = f"; and {len(errors) - 20} more" if len(errors) > 20 else ""
            raise DeployExecutionError(
                f"Pages projection has broken links: {preview}{suffix}"
            )

    @staticmethod
    def _resolve_missing_reference(
        origin: str,
        base_path: str,
        document_base: str,
        value: str,
        pages_site: Path,
    ) -> tuple[Path, Path] | None:
        reference = value.strip()
        if not reference or reference.startswith(
            ("#", "data:", "javascript:", "mailto:")
        ):
            return None
        resolved = urlsplit(urljoin(document_base, reference))
        if (
            resolved.scheme not in {"http", "https"}
            or resolved.netloc != "reasbook.invalid"
        ):
            return None
        path = unquote(resolved.path)
        root_request = path.rstrip("/") == base_path.rstrip("/")
        if root_request:
            relative = Path("index.html")
        elif path.startswith(base_path):
            relative_text = path[len(base_path) :].lstrip("/")
            relative_url = PurePosixPath(relative_text or "index.html")
            if (
                relative_url.is_absolute()
                or any(part in {"", ".", ".."} for part in relative_url.parts)
                or "\\" in relative_text
                or "\x00" in relative_text
            ):
                raise DeployExecutionError(
                    f"Pages link has an unsafe internal path: {value}"
                )
            relative = Path(*relative_url.parts)
        else:
            raise DeployExecutionError(
                f"Pages link escapes configured base path {base_path}: {value}"
            )
        target = pages_site / relative
        if pages_site not in target.resolve(strict=False).parents:
            raise DeployExecutionError(
                f"Pages link escapes the projected site: {value}"
            )
        if (path.endswith("/") and not root_request) or target.is_dir():
            target = target / "index.html"
            relative = relative / "index.html"
        if target.is_file():
            return None
        return relative, target

    @staticmethod
    def _is_omitted_dependency_doc(relative: Path) -> bool:
        parts = relative.parts
        return len(parts) >= 4 and parts[0] == "versions" and parts[2] == "docs"

    @staticmethod
    def _write_dependency_stub(path: Path, base_path: str) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        home = html.escape(base_path, quote=True)
        path.write_text(
            "\n".join(
                [
                    "<!doctype html>",
                    '<html lang="en">',
                    "<head>",
                    '  <meta charset="utf-8" />',
                    '  <meta name="viewport" '
                    'content="width=device-width,initial-scale=1" />',
                    "  <title>Dependency documentation</title>",
                    f'  <link rel="stylesheet" href="{home}static/catalog.css" />',
                    "</head>",
                    "<body>",
                    '  <main class="page-shell narrow-shell">',
                    '    <p class="eyebrow">Canonical Pages Projection</p>',
                    "    <h1>Dependency documentation</h1>",
                    "    <p>This API page is outside the selected project roots. "
                    "The project documentation, source, and theorem map remain "
                    "available.</p>",
                    f'    <p><a class="back-link" href="{home}">'
                    "Back to ReasBook</a></p>",
                    "  </main>",
                    "</body>",
                    "</html>",
                    "",
                ]
            ),
            encoding="utf-8",
        )

    @staticmethod
    def _validate_required_content(spec: ReleaseSpec, site: Path) -> None:
        required = [site / "index.html", site / "release-spec.json"]
        for project in spec.canonical_projects():
            required.append(site / "sites" / project.slug / "index.html")
            if "theorem_graph" in project.outputs:
                required.append(
                    site
                    / "theorem-maps"
                    / project.kind
                    / project.slug
                    / "index.html"
                )
        missing = [
            str(path.relative_to(site))
            for path in required
            if not path.is_file()
        ]
        if missing:
            raise DeployExecutionError(
                "Pages projection is missing canonical content: " + ", ".join(missing)
            )

    @staticmethod
    def _validate_site(root: Path) -> None:
        if not root.is_dir() or root.is_symlink():
            raise DeployExecutionError(f"site tree is not a directory: {root}")
        for path in root.rglob("*"):
            if path.is_symlink():
                raise DeployExecutionError(f"site tree contains a symlink: {path}")
            if not path.is_file() and not path.is_dir():
                raise DeployExecutionError(f"site tree contains a special file: {path}")

    @staticmethod
    def _publish(staged: Path, target: Path, backup: Path) -> None:
        had_target = target.exists() or target.is_symlink()
        if had_target:
            os.replace(target, backup)
        try:
            os.replace(staged, target)
        except OSError:
            if had_target and not (target.exists() or target.is_symlink()):
                os.replace(backup, target)
            raise
        if had_target:
            if backup.is_dir() and not backup.is_symlink():
                shutil.rmtree(backup)
            else:
                backup.unlink(missing_ok=True)


def create_release_set(
    layout: ReleaseLayout,
    store: ReleaseStore,
    spec: ReleaseSpec,
    policies: tuple[ReleaseArtifactPolicy, ...],
    bundles: tuple[BundleInfo, ...],
) -> tuple[ReleaseSetManifest, tuple[BundleInfo, ...]]:
    """Persist a portable manifest that binds both target artifacts."""

    records: list[ReleaseArtifactRecord] = []
    for bundle in sorted(bundles, key=lambda item: item.artifact):
        value = json.loads(Path(bundle.manifest).read_text(encoding="utf-8"))
        manifest = ReleaseManifest.from_dict(value)
        if (
            bundle.release_id != spec.release_id
            or manifest.release_id != spec.release_id
            or manifest.spec_digest != spec.spec_digest
            or manifest.artifact != bundle.artifact
        ):
            raise DeployExecutionError("artifact manifest does not match its bundle")
        records.append(
            ReleaseArtifactRecord(
                name=bundle.artifact,
                bundle=Path(bundle.bundle).name,
                bundle_sha256=bundle.bundle_sha256,
                site_tree_sha256=manifest.site_tree_sha256,
                file_count=manifest.file_count,
                total_bytes=manifest.total_bytes,
            )
        )
    release_set = ReleaseSetManifest(
        release_id=spec.release_id,
        spec_digest=spec.spec_digest,
        generated_at=spec.resolved_at,
        artifact_policy_sha256=artifact_policy_digest(policies),
        artifacts=tuple(records),
    )
    store.write_release_set(release_set)
    updated = tuple(
        replace(bundle, release_set=str(layout.release_set)) for bundle in bundles
    )
    for bundle in updated:
        if bundle.artifact == "pages":
            store.write_pages_bundle_info(bundle)
        elif bundle.artifact == "full":
            store.write_bundle_info(bundle)
    return release_set, updated


__all__ = [
    "PagesSiteProjector",
    "artifact_policy_digest",
    "create_release_set",
]
