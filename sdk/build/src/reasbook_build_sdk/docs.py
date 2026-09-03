"""Bounded-memory API documentation builds for selected ReasBook roots."""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
import fcntl
import hashlib
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import re
import shutil
import tempfile
from typing import Iterator, Protocol
from urllib.parse import quote, unquote, urljoin, urlsplit
import uuid

from .command import Command, CommandResult
from .errors import BuildFailed, ConfigurationError
from .executor import SubprocessRunner
from .project import discover_project


_MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:[.][A-Za-z_][A-Za-z0-9_']*)*$")
_GITHUB_RE = re.compile(r"^https://github[.]com/[^/]+/[^/]+?(?:[.]git)?$")
_PROFILE = "project-roots-v1"


class _Runner(Protocol):
    def run(self, command: Command) -> CommandResult:
        """Run one documentation command."""


class _LinkParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.base_href: str | None = None
        self.references: list[str] = []

    def handle_starttag(
        self, tag: str, attrs: list[tuple[str, str | None]]
    ) -> None:
        values = dict(attrs)
        if tag == "base" and self.base_href is None and values.get("href"):
            self.base_href = values["href"]
        for attribute in ("href", "src"):
            if values.get(attribute):
                self.references.append(values[attribute] or "")


@dataclass(frozen=True)
class ProjectDocsResult:
    output_root: Path
    mode: str
    targets: tuple[str, ...]
    pages: tuple[Path, ...]
    dependency_stubs: int
    reused: bool

    def public_dict(self) -> dict[str, object]:
        return {
            "output_root": str(self.output_root),
            "mode": self.mode,
            "targets": list(self.targets),
            "pages": [str(path) for path in self.pages],
            "dependency_stubs": self.dependency_stubs,
            "reused": self.reused,
        }


class ProjectDocumentationBuilder:
    """Generate only selected root-module docs in an immutable cache entry.

    doc-gen4 historically rendered every transitive Mathlib page and then
    assembled one global in-memory index. That is unnecessary for ReasBook's
    per-project entry pages and exceeds common CI/container memory limits.
    This adapter invokes doc-gen4's single-module API and builds a small index
    from only the requested roots. Missing dependency pages become explicit
    local placeholders, so both Pages and self-hosted artifacts remain
    navigable without silently publishing broken links.
    """

    def __init__(self, runner: _Runner | None = None) -> None:
        self.runner = runner or SubprocessRunner(stream=True)

    def build(
        self,
        project_root: str | Path,
        targets: tuple[str, ...] | list[str],
        output_root: str | Path,
        *,
        lake_bin: str = "lake",
        repository: str = "",
        revision: str = "",
        timeout_seconds: float = 21600.0,
    ) -> ProjectDocsResult:
        project = discover_project(project_root)
        modules = self._normalize_targets(targets)
        if not lake_bin.strip() or any(char in lake_bin for char in "\x00\r\n"):
            raise ConfigurationError("lake executable must be a safe non-empty value")
        if timeout_seconds <= 0:
            raise ConfigurationError("documentation timeout must be positive")
        repository = repository.strip().removesuffix(".git")
        revision = revision.strip()
        if repository and not _GITHUB_RE.fullmatch(repository):
            raise ConfigurationError("documentation repository must be a GitHub HTTPS URL")
        if revision and not re.fullmatch(r"[0-9a-f]{40}", revision):
            raise ConfigurationError("documentation revision must be a full commit SHA")
        if bool(repository) != bool(revision):
            raise ConfigurationError(
                "documentation repository and revision must be provided together"
            )

        target = Path(output_root).expanduser().resolve(strict=False)
        if target in {Path("/"), project.root} or target in project.root.parents:
            raise ConfigurationError(f"unsafe documentation output root: {target}")
        if target.is_symlink():
            raise ConfigurationError(f"documentation output must not be a symlink: {target}")
        target.parent.mkdir(parents=True, exist_ok=True)

        docgen, mode = self._docgen(project.root, lake_bin, timeout_seconds)
        identity = {
            "schema_version": 1,
            "profile": _PROFILE,
            "toolchain": project.toolchain,
            "targets": list(modules),
            "repository": repository,
            "revision": revision,
            "docgen_sha256": self._sha256(docgen),
            "mode": mode,
        }
        lock = target.parent / f".{target.name}.lock"
        with self._exclusive_lock(lock):
            cached = self._cached_result(target, identity, modules, mode)
            if cached is not None:
                return cached
            return self._build_fresh(
                project.root,
                target,
                modules,
                docgen,
                mode,
                identity,
                lake_bin=lake_bin,
                repository=repository,
                revision=revision,
                timeout_seconds=timeout_seconds,
            )

    def _build_fresh(
        self,
        project_root: Path,
        target: Path,
        modules: tuple[str, ...],
        docgen: Path,
        mode: str,
        identity: dict[str, object],
        *,
        lake_bin: str,
        repository: str,
        revision: str,
        timeout_seconds: float,
    ) -> ProjectDocsResult:
        stage = Path(
            tempfile.mkdtemp(prefix=f".{target.name}.stage-", dir=target.parent)
        )
        backup = target.parent / f".{target.name}.backup-{uuid.uuid4().hex}"
        try:
            for module in modules:
                source = self._module_source(project_root, module)
                source_uri = self._source_uri(
                    project_root, source, repository, revision
                )
                argv = [
                    lake_bin,
                    "-R",
                    "-Kenv=dev",
                    "env",
                    str(docgen),
                    "single",
                    "--build",
                    str(stage),
                    module,
                ]
                if mode == "database":
                    argv.append("api-docs.db")
                argv.append(source_uri)
                self._run(project_root, tuple(argv), timeout_seconds)

            if mode == "database":
                database = stage / "api-docs.db"
                if not database.is_file() or database.stat().st_size == 0:
                    raise BuildFailed("doc-gen4 did not create its documentation database")
                self._run(
                    project_root,
                    (
                        lake_bin,
                        "-R",
                        "-Kenv=dev",
                        "env",
                        str(docgen),
                        "fromDb",
                        "--build",
                        str(stage),
                        "--manifest",
                        str(stage / "doc-manifest.json"),
                        str(database),
                    ),
                    timeout_seconds,
                )
            else:
                self._run(
                    project_root,
                    (
                        lake_bin,
                        "-R",
                        "-Kenv=dev",
                        "env",
                        str(docgen),
                        "index",
                        "--build",
                        str(stage),
                    ),
                    timeout_seconds,
                )

            pages = self._expected_pages(stage, modules)
            self._validate_pages(pages)
            stub_count = self._close_documentation_links(stage / "doc")
            (stage / "project-docs.json").write_text(
                json.dumps(identity, ensure_ascii=True, sort_keys=True, indent=2)
                + "\n",
                encoding="utf-8",
            )
            self._validate_tree(stage)
            had_target = target.exists()
            if had_target:
                os.replace(target, backup)
            try:
                os.replace(stage, target)
            except OSError:
                if had_target and not target.exists():
                    os.replace(backup, target)
                raise
            if had_target:
                self._remove_path(backup)
            return ProjectDocsResult(
                target,
                mode,
                modules,
                self._expected_pages(target, modules),
                stub_count,
                False,
            )
        finally:
            if stage.exists():
                shutil.rmtree(stage)
            # Preserve the backup for manual recovery if both publication and
            # rollback fail.  If either operation succeeded, ``target`` exists
            # and the backup is no longer needed.
            if backup.exists() and target.exists():
                self._remove_path(backup)

    def _docgen(
        self, project_root: Path, lake_bin: str, timeout_seconds: float
    ) -> tuple[Path, str]:
        package = project_root / ".lake" / "packages" / "doc-gen4"
        executable = package / ".lake" / "build" / "bin" / "doc-gen4"
        if not executable.is_file():
            self._run(
                project_root,
                (lake_bin, "-R", "-Kenv=dev", "build", "doc-gen4"),
                timeout_seconds,
            )
        if not executable.is_file() or not os.access(executable, os.X_OK):
            raise BuildFailed(f"doc-gen4 executable is missing: {executable}")
        main = package / "Main.lean"
        try:
            source = main.read_text(encoding="utf-8")
        except OSError as exc:
            raise BuildFailed(f"cannot inspect doc-gen4 interface: {main}") from exc
        mode = "database" if re.search(r"\bfromDb\b", source) else "legacy"
        return executable.resolve(), mode

    def _run(
        self, cwd: Path, argv: tuple[str, ...], timeout_seconds: float
    ) -> None:
        result = self.runner.run(
            Command(
                argv=argv,
                cwd=cwd,
                env={"DISABLE_EQUATIONS": "1", "LEAN_NUM_THREADS": "1"},
                timeout=timeout_seconds,
            )
        )
        if result.returncode != 0:
            detail = (result.stderr or result.stdout).strip()
            raise BuildFailed(
                "documentation command failed"
                + (f": {detail[-1000:]}" if detail else "")
            )

    @staticmethod
    def _normalize_targets(values: tuple[str, ...] | list[str]) -> tuple[str, ...]:
        modules: list[str] = []
        for value in values:
            module = str(value).strip().split(":", 1)[0]
            if not _MODULE_RE.fullmatch(module):
                raise ConfigurationError(f"invalid documentation module: {value!r}")
            if module not in modules:
                modules.append(module)
        if not modules:
            raise ConfigurationError("at least one documentation module is required")
        return tuple(modules)

    @staticmethod
    def _module_source(project_root: Path, module: str) -> Path:
        parts = module.split(".")
        relative = Path(*parts).with_suffix(".lean")
        candidates = [project_root / relative]
        if parts[0] not in {"Books", "Papers"}:
            candidates.extend(
                (project_root / kind / relative for kind in ("Books", "Papers"))
            )
        matches = [path for path in candidates if path.is_file()]
        if not matches and len(parts) == 1:
            matches = sorted(project_root.glob(f"Books/**/{parts[0]}.lean"))
            matches += sorted(project_root.glob(f"Papers/**/{parts[0]}.lean"))
        if len(matches) != 1:
            raise BuildFailed(
                f"cannot uniquely resolve source file for documentation module {module}"
            )
        return matches[0].resolve()

    @staticmethod
    def _source_uri(
        project_root: Path, source: Path, repository: str, revision: str
    ) -> str:
        if not repository:
            return "#"
        relative = source.relative_to(project_root).as_posix()
        return f"{repository}/blob/{revision}/ReasBook/{quote(relative, safe='/')}"

    @staticmethod
    def _expected_pages(root: Path, modules: tuple[str, ...]) -> tuple[Path, ...]:
        return tuple(root / "doc" / Path(*module.split(".")).with_suffix(".html") for module in modules)

    @staticmethod
    def _validate_pages(pages: tuple[Path, ...]) -> None:
        missing = []
        for page in pages:
            try:
                content = page.read_text(encoding="utf-8", errors="replace")
            except OSError:
                content = ""
            if page.is_symlink() or len(content.strip()) < 64 or "<html" not in content.lower():
                missing.append(str(page))
        if missing:
            raise BuildFailed(
                "documentation output is missing or invalid: " + ", ".join(missing)
            )

    @classmethod
    def _cached_result(
        cls,
        target: Path,
        identity: dict[str, object],
        modules: tuple[str, ...],
        mode: str,
    ) -> ProjectDocsResult | None:
        marker = target / "project-docs.json"
        try:
            cached_identity = json.loads(marker.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return None
        pages = cls._expected_pages(target, modules)
        try:
            cls._validate_pages(pages)
            cls._validate_tree(target)
        except BuildFailed:
            return None
        if cached_identity != identity:
            return None
        stubs = sum(1 for path in (target / "doc").rglob("*.html") if cls._is_stub(path))
        return ProjectDocsResult(target, mode, modules, pages, stubs, True)

    @classmethod
    def _close_documentation_links(cls, doc_root: Path) -> int:
        if not (doc_root / "index.html").is_file():
            raise BuildFailed("documentation output has no index.html")
        missing_assets: list[str] = []
        stubs: set[Path] = set()
        for document in sorted(doc_root.rglob("*.html")):
            parser = _LinkParser()
            parser.feed(document.read_text(encoding="utf-8", errors="replace"))
            document_url = "https://docs.invalid/" + document.relative_to(doc_root).as_posix()
            base_url = urljoin(document_url, parser.base_href or "")
            for value in parser.references:
                reference = value.strip()
                if not reference or reference.startswith(("#", "data:", "javascript:", "mailto:")):
                    continue
                resolved = urlsplit(urljoin(base_url, reference))
                if resolved.netloc != "docs.invalid":
                    continue
                relative_text = unquote(resolved.path).lstrip("/")
                if not relative_text or "\\" in relative_text or "\x00" in relative_text:
                    continue
                relative = Path(relative_text)
                if any(part in {"", ".", ".."} for part in relative.parts):
                    raise BuildFailed(f"documentation link has an unsafe path: {value}")
                target = (doc_root / relative).resolve(strict=False)
                if doc_root not in target.parents:
                    raise BuildFailed(f"documentation link escapes its root: {value}")
                if resolved.path.endswith("/") or target.is_dir():
                    target /= "index.html"
                if target.is_file():
                    continue
                if target.suffix.lower() in {".html", ".htm"}:
                    cls._write_stub(doc_root, target)
                    stubs.add(target)
                else:
                    missing_assets.append(
                        f"{document.relative_to(doc_root)} -> {value}"
                    )
        if missing_assets:
            raise BuildFailed(
                "documentation output references missing assets: "
                + "; ".join(missing_assets[:20])
            )
        return len(stubs)

    @staticmethod
    def _write_stub(doc_root: Path, path: Path) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        depth = len(path.relative_to(doc_root).parts) - 1
        prefix = "../" * depth
        path.write_text(
            "\n".join(
                (
                    "<!doctype html>",
                    '<html lang="en">',
                    "<head>",
                    '  <meta charset="utf-8" />',
                    '  <meta name="viewport" content="width=device-width,initial-scale=1" />',
                    "  <title>Dependency documentation</title>",
                    f'  <link rel="stylesheet" href="{prefix}style.css" />',
                    "</head>",
                    '<body data-reasbook-doc-stub="true">',
                    "  <main>",
                    "    <h1>Dependency documentation</h1>",
                    "    <p>This API page is outside the selected ReasBook project roots. "
                    "The project documentation, source, and theorem map remain available.</p>",
                    f'    <p><a href="{prefix}index.html">Documentation index</a></p>',
                    "  </main>",
                    "</body>",
                    "</html>",
                    "",
                )
            ),
            encoding="utf-8",
        )

    @staticmethod
    def _is_stub(path: Path) -> bool:
        try:
            return 'data-reasbook-doc-stub="true"' in path.read_text(
                encoding="utf-8", errors="ignore"
            )
        except OSError:
            return False

    @staticmethod
    def _validate_tree(root: Path) -> None:
        if not root.is_dir() or root.is_symlink():
            raise BuildFailed(f"documentation cache is not a directory: {root}")
        for path in root.rglob("*"):
            if path.is_symlink() or (not path.is_file() and not path.is_dir()):
                raise BuildFailed(f"documentation cache contains an unsafe file: {path}")

    @staticmethod
    def _sha256(path: Path) -> str:
        digest = hashlib.sha256()
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
        return digest.hexdigest()

    @staticmethod
    def _remove_path(path: Path) -> None:
        if path.is_dir() and not path.is_symlink():
            shutil.rmtree(path)
        else:
            path.unlink(missing_ok=True)

    @staticmethod
    @contextmanager
    def _exclusive_lock(path: Path) -> Iterator[None]:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a+b") as handle:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


__all__ = ["ProjectDocumentationBuilder", "ProjectDocsResult"]
