"""Resolve ReasBook release evidence without copying build trees.

The reviewer keeps review state local, while Lean source, doc-gen pages, Verso
pages, and theorem-map data stay in the release cache produced by ReasBook's
deploy pipeline.  This module is deliberately read-only and treats every
release path as untrusted filesystem input.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path, PurePosixPath
import re
from typing import Any

from settings import release_root
from theorem_graph_sdk.generator import RESOURCE_ROOT
from verso_selection import selected_verso

GRAPH_ASSETS = RESOURCE_ROOT / "assets"


_SAFE_PART = re.compile(r"^[A-Za-z0-9_.-]+$")
_HTML_SUFFIXES = {".html", ".htm"}


def _curated_items(script: str) -> list[dict[str, Any]] | None:
    """Read the historical ITEMS literal without evaluating JavaScript.

    Only JSON values and unquoted object keys are accepted. Calls, variable
    references, comments and executable expressions fail closed.
    """
    assignment = re.search(r"\b(?:var|const|let)\s+ITEMS\s*=\s*\[", script)
    if assignment is None:
        return None
    position = assignment.end() - 1
    tokens: list[str] = []
    depth = 0
    decoder = json.JSONDecoder()
    while position < len(script):
        char = script[position]
        if char.isspace():
            position += 1
            continue
        if char == '"':
            try:
                value, length = decoder.raw_decode(script[position:])
            except ValueError:
                return None
            tokens.append(json.dumps(value))
            position += length
            continue
        if char in "[]{}:,":
            tokens.append(char)
            depth += (char in "[{") - (char in "]}")
            position += 1
            if depth == 0:
                break
            continue
        identifier = re.match(r"[A-Za-z_$][A-Za-z0-9_$]*", script[position:])
        if identifier:
            word = identifier.group()
            position += len(word)
            if re.match(r"\s*:", script[position:]):
                tokens.append(json.dumps(word))
            elif word in {"true", "false", "null"}:
                tokens.append(word)
            else:
                return None
            continue
        number = re.match(r"-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?", script[position:])
        if number is None:
            return None
        tokens.append(number.group())
        position += len(number.group())
    try:
        items = json.loads("".join(tokens))
    except ValueError:
        return None
    return items if isinstance(items, list) and all(isinstance(item, dict) for item in items) else None
_DECLARATION_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|opaque|macro|syntax)\s+)*"
    r"(?P<kind>theorem|lemma|example|def|abbrev|structure|class|inductive|axiom|instance|opaque)\b"
    r"\s+(?P<name>[^\s(:={]+)"
)


def _declaration_assignment(block: str) -> int:
    """Return the declaration-level ``:=`` in a bounded Lean block.

    A declaration can contain a ``let`` binding in its type, so the first
    assignment token is not necessarily the declaration's value separator.
    Prefer the separator before a tactic body and otherwise use indentation
    as a structural cue, while ignoring strings and comments.
    """

    lines = block.splitlines(keepends=True)
    first_line = next((line for line in lines if line.strip()), "")
    base_indent = len(first_line) - len(first_line.lstrip(" \t"))
    state = "normal"
    block_comment_depth = 0
    line_start = True
    line_indent = 0
    candidates: list[tuple[int, int]] = []
    index = 0
    while index < len(block) - 1:
        char = block[index]
        next_char = block[index + 1]
        if line_start:
            if char in " \t":
                line_indent += 1
                index += 1
                continue
            line_start = False
        if state == "line-comment":
            if char == "\n":
                state = "normal"
                line_start = True
                line_indent = 0
            index += 1
            continue
        if state == "block-comment":
            if char == "/" and next_char == "-":
                block_comment_depth += 1
                index += 2
                continue
            if char == "-" and next_char == "/":
                block_comment_depth -= 1
                state = "normal" if block_comment_depth == 0 else "block-comment"
                index += 2
                continue
            if char == "\n":
                line_start = True
                line_indent = 0
            index += 1
            continue
        if state == "string":
            if char == "\\":
                index += 2
                continue
            if char == '"':
                state = "normal"
            if char == "\n":
                line_start = True
                line_indent = 0
            index += 1
            continue
        if char == "-" and next_char == "-":
            state = "line-comment"
            index += 2
            continue
        if char == "/" and next_char == "-":
            state = "block-comment"
            block_comment_depth = 1
            index += 2
            continue
        if char == '"':
            state = "string"
            index += 1
            continue
        if char == ":" and next_char == "=":
            candidates.append((index, line_indent))
        if char == "\n":
            line_start = True
            line_indent = 0
        index += 1
    # The declaration separator for theorem-like declarations is commonly
    # followed by ``by``. Prefer that marker so a preceding ``let x := ...``
    # cannot truncate the contract. For term-valued declarations, use the
    # last candidate at the declaration indentation as a conservative fallback.
    for position, _indent in candidates:
        if re.match(r"\s*by(?:\s|$)", block[position + 2 :]):
            return position
    aligned = [position for position, indent in candidates if indent <= base_indent]
    if aligned:
        return aligned[-1]
    if candidates:
        return candidates[-1][0]
    return -1


@dataclass(frozen=True)
class ReleaseEvidence:
    release_id: str
    branch: str
    commit: str
    site_root: Path
    source_root: Path | None
    project_id: str
    project_kind: str
    docs_root: Path
    graph_root: Path
    graph_path: Path | None
    verso_release_id: str = ""

    @property
    def site_available(self) -> bool:
        return self.site_root.is_dir()

    @property
    def docs_available(self) -> bool:
        return self.docs_root.is_dir()

    @property
    def source_available(self) -> bool:
        return bool(self.source_root and self.source_root.is_dir())

    @property
    def graph_available(self) -> bool:
        return bool(self.graph_path and self.graph_path.is_file())


class EvidenceResolver:
    """Find the newest successful release evidence for one catalog entry."""

    def __init__(
        self, book: dict[str, Any], *, project_root: Path, data_root: Path,
        index_path: Path | None = None,
    ) -> None:
        self.book = book
        self.project_root = project_root.resolve()
        self.data_root = data_root.resolve()
        self.index_path = index_path or self.data_root / "books" / str(book.get("slug") or "") / "index.json"
        self.release_root = release_root()
        project_path = str(book.get("projectPath") or "")
        self.project_id = Path(project_path).name or str(book.get("slug") or "")
        self.project_kind = "papers" if str(book.get("kind")) == "paper" else "books"
        self.branch = self._index_meta("branch") or self._first_branch()
        # Older lightweight indexes can carry the source checkout commit while
        # the release manifest records the commit used for the published
        # artifacts. Keep the indexed value for candidate preference, then
        # replace it with the selected release's authoritative project commit.
        self.requested_commit = self._index_meta("commit") or ""
        self.commit = self.requested_commit
        self._evidence: ReleaseEvidence | None = None
        self._graph_payload: dict[str, Any] | None = None

    @staticmethod
    def _graph_quality(payload: dict[str, Any] | None) -> tuple[int, int, int, int]:
        """Rank graph evidence without mistaking source indexes for dependencies."""

        if not isinstance(payload, dict):
            return (-1, 0, 0, 0)
        generation = payload.get("generation")
        mode = str(generation.get("mode") or "") if isinstance(generation, dict) else ""
        # Curated maps predate the generation marker and remain authoritative.
        mode_rank = {
            "source-fallback": 0,
            "lean-environment-partial": 2,
            "lean-environment": 3,
            "curated": 4,
            "curated-static": 4,
        }.get(mode, 4 if not mode else 1)
        compiled_modes = {"lean-environment", "lean-environment-partial"}
        items = payload.get("items") if isinstance(payload.get("items"), list) else []
        typed_rank = int(
            mode in compiled_modes
            and payload.get("schemaVersion") == 2
            and isinstance(generation, dict)
            and generation.get("dependencyModel") == "statement-and-proof-v1"
        )
        edges = sum(
            len(item.get("dependencies"))
            for item in items
            if isinstance(item, dict) and isinstance(item.get("dependencies"), list)
        )
        return (mode_rank, typed_rank, edges, len(items))

    @staticmethod
    def _read_graph(path: Path | None) -> dict[str, Any] | None:
        if path is None or not path.is_file():
            return None
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError, TypeError):
            return None
        return payload if isinstance(payload, dict) else None

    def _read_curated_graph(self, root: Path, commit: str) -> dict[str, Any] | None:
        metadata = self._read_graph(root / "metadata.json")
        if not metadata or metadata.get("schemaVersion") != 1 or not (root / "index.html").is_file():
            return None
        project = metadata.get("project")
        generation = metadata.get("generation")
        if not isinstance(project, dict) or not isinstance(generation, dict):
            return None
        if generation.get("mode") not in {"curated", "curated-static"} or not commit:
            return None
        if any(project.get(key) != expected for key, expected in (
            ("id", self.project_id), ("kind", self.project_kind), ("branch", self.branch), ("commit", commit),
        )):
            return None
        try:
            app_path = root / "app.js"
            if app_path.stat().st_size > 2 * 1024 * 1024:
                return None
            items = _curated_items(app_path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError):
            return None
        if not items:
            return None
        ids = {item.get("id") for item in items if isinstance(item.get("id"), str)}
        if len(ids) != len(items):
            return None
        edges = 0
        for item in items:
            dependencies = item.get("dependencies")
            if not isinstance(dependencies, list) or any(not isinstance(dep, str) or dep not in ids for dep in dependencies):
                return None
            edges += len(dependencies)
        if metadata.get("nodes") != len(items) or metadata.get("edges") != edges:
            return None
        return {**metadata, "items": [{**item, "dependencyEvidence": "curated"} for item in items]}

    @staticmethod
    def _graph_has_items(payload: dict[str, Any] | None) -> bool:
        return bool(
            isinstance(payload, dict)
            and isinstance(payload.get("items"), list)
            and payload["items"]
        )

    def _cached_graph(self, slug: str, commit: str) -> tuple[Path, Path, dict[str, Any]] | None:
        """Return a generated compiled graph only when its release identity matches."""

        if not _SAFE_PART.fullmatch(slug):
            return None
        root = (self.data_root / "books" / slug / "theorem-map").resolve()
        expected_parent = (self.data_root / "books" / slug).resolve()
        if root.parent != expected_parent or not (root / "index.html").is_file():
            return None
        path = root / "data.json"
        payload = self._read_graph(path)
        if not self._graph_has_items(payload):
            return None
        assert payload is not None
        project = payload.get("project") if isinstance(payload.get("project"), dict) else {}
        generation = payload.get("generation") if isinstance(payload.get("generation"), dict) else {}
        mode = str(generation.get("mode") or "")
        if mode not in {"lean-environment", "lean-environment-partial"}:
            return None
        if mode == "lean-environment-partial" and not (
            payload.get("schemaVersion") == 2
            and generation.get("dependencyModel") == "statement-and-proof-v1"
            and generation.get("dependencyCoverage") == "partial"
        ):
            return None
        if str(project.get("id") or "") != self.project_id:
            return None
        if str(project.get("kind") or "") != self.project_kind:
            return None
        if str(project.get("branch") or "") != self.branch:
            return None
        cached_commit = str(project.get("commit") or "")
        if commit and cached_commit != commit:
            return None
        return root, path, payload

    def _first_branch(self) -> str:
        branches = self.book.get("branches")
        return str(branches[0]) if isinstance(branches, list) and branches else ""

    def _index_meta(self, key: str) -> str:
        try:
            payload = json.loads(self.index_path.read_text(encoding="utf-8"))
        except (OSError, ValueError, TypeError):
            return ""
        value = payload.get(key) if isinstance(payload, dict) else None
        return str(value).strip() if value else ""

    def _release_project_commit(self, release: Path) -> str:
        """Return the release manifest commit for this project and branch.

        The review index is intentionally lightweight and may have been built
        before the deploy release was finalized. Release metadata is the
        authority for pairing source, docs, Verso, and graph evidence.
        """

        slug = str(self.book.get("slug") or "")
        spec = release / "release-spec.json"
        try:
            payload = json.loads(spec.read_text(encoding="utf-8"))
        except (OSError, ValueError, TypeError):
            payload = {}
        projects = payload.get("projects") if isinstance(payload, dict) else None
        if isinstance(projects, list):
            for project in projects:
                if not isinstance(project, dict):
                    continue
                project_slug = str(project.get("slug") or "")
                project_id = str(project.get("project_id") or "")
                project_branch = str(project.get("branch") or "")
                if project_branch == self.branch and (project_slug == slug or project_id == self.project_id):
                    commit = str(project.get("commit") or "").strip()
                    if commit:
                        return commit
        branches = payload.get("branches") if isinstance(payload, dict) else None
        if isinstance(branches, list):
            for branch in branches:
                if isinstance(branch, dict) and str(branch.get("name") or "") == self.branch:
                    commit = str(branch.get("commit") or "").strip()
                    if commit:
                        return commit
        result = release / "branches" / self.branch / "result.json"
        try:
            result_payload = json.loads(result.read_text(encoding="utf-8"))
        except (OSError, ValueError, TypeError):
            result_payload = {}
        return str(result_payload.get("commit") or "").strip() if isinstance(result_payload, dict) else ""

    def _release_lists_project(self, release: Path) -> bool:
        """Check project membership without mistaking a branch commit for membership."""

        try:
            payload = json.loads((release / "release-spec.json").read_text(encoding="utf-8"))
        except (OSError, ValueError, TypeError):
            return False
        projects = payload.get("projects") if isinstance(payload, dict) else None
        if not isinstance(projects, list):
            return False
        slug = str(self.book.get("slug") or "")
        return any(
            isinstance(project, dict)
            and project.get("branch") == self.branch
            and project.get("kind", self.project_kind) == self.project_kind
            and (project.get("slug") == slug or project.get("project_id") == self.project_id)
            for project in projects
        )

    def resolve(self) -> ReleaseEvidence | None:
        if self._evidence is not None:
            return self._evidence
        if not self.release_root.is_dir() or not self.branch:
            return None
        slug = str(self.book.get("slug") or "")
        # A supplemental typed graph can legitimately belong to a branch
        # release which did not build this book (for example Probability).
        # Only a matching immutable commit can supply that missing membership.
        indexed_graph = self._cached_graph(slug, self.requested_commit) if self.requested_commit else None
        candidates: list[tuple[int, float, Path, Path, str]] = []
        try:
            releases = [path for path in self.release_root.iterdir() if path.is_dir()]
        except OSError:
            releases = []
        for release in sorted(releases, key=lambda value: value.stat().st_mtime, reverse=True):
            # A directory can exist while its finalizer is still running (or
            # after a failed attempt).  Only a successful branch result whose
            # immutable identity agrees with the ReleaseSpec may provide
            # review evidence.
            site = release / "branches" / self.branch / "site"
            if not site.is_dir():
                continue
            try:
                spec_payload = json.loads((release / "release-spec.json").read_text(encoding="utf-8"))
                result_payload = json.loads((release / "branches" / self.branch / "result.json").read_text(encoding="utf-8"))
            except (OSError, ValueError, TypeError):
                continue
            if not isinstance(spec_payload, dict) or not isinstance(result_payload, dict):
                continue
            if str(spec_payload.get("release_id") or "") != release.name:
                continue
            if (
                result_payload.get("schema_version") != 1
                or result_payload.get("status") != "success"
                or result_payload.get("error") is not None
                or str(result_payload.get("release_id") or "") != release.name
                or str(result_payload.get("branch") or "") != self.branch
                or str(result_payload.get("site_root") or "") != str(site.resolve())
                or str(result_payload.get("spec_digest") or "") != str(spec_payload.get("spec_digest") or "")
            ):
                continue
            branch_spec = next(
                (entry for entry in spec_payload.get("branches", [])
                 if isinstance(entry, dict) and str(entry.get("name") or "") == self.branch),
                None,
            )
            if not isinstance(branch_spec, dict) or str(result_payload.get("commit") or "") != str(branch_spec.get("commit") or ""):
                continue
            # Branch result validation establishes the immutable environment.
            # Project membership is checked below using project artifacts or a
            # matching supplemental graph: successful branch releases may omit
            # a book whose typed graph was extracted separately afterward.
            graph = site / "theorem-maps" / self.project_kind / slug / "data.json"
            docs = site / "docs" / "ReasBook"
            release_commit = self._release_project_commit(release)
            project_docs = (
                docs / self.project_id,
                docs / f"{self.project_id}.html",
                docs / self.project_kind.title() / self.project_id,
                docs / "ReasBook" / self.project_kind.title() / self.project_id,
            )
            has_project_evidence = (
                graph.is_file()
                or self._read_curated_graph(graph.parent, release_commit) is not None
                or (site / slug).is_dir()
                or (site / self.project_kind / slug).is_dir()
                or any(path.is_dir() or path.is_file() for path in project_docs)
                or (docs.is_dir() and self._release_lists_project(release))
                or (indexed_graph is not None and release_commit == self.requested_commit)
            )
            if not has_project_evidence:
                continue
            commit_match = int(bool(self.requested_commit and release_commit == self.requested_commit))
            candidates.append((commit_match, release.stat().st_mtime, release, site, release_commit))
        if not candidates:
            return None
        _match, _mtime, release, site, release_commit = sorted(
            candidates, reverse=True, key=lambda item: (item[0], item[1])
        )[0]
        commit = release_commit or self.requested_commit
        source_root = release / "worktrees" / self.branch / "ReasBook" / self.project_kind.title() / self.project_id
        if not self._source_candidate_matches(release, source_root, commit):
            source_root = next(
                (
                    candidate
                    for older in sorted(releases, key=lambda value: value.stat().st_mtime, reverse=True)
                    if self._source_candidate_matches(
                        older,
                        candidate := older
                        / "worktrees"
                        / self.branch
                        / "ReasBook"
                        / self.project_kind.title()
                        / self.project_id,
                        commit,
                        require_identity=True,
                    )
                ),
                None,
            )
        graph_root = site / "theorem-maps" / self.project_kind / slug
        graph_path = graph_root / "data.json"
        release_graph = self._read_graph(graph_path)
        if not self._graph_has_items(release_graph):
            graph_path = None
            release_graph = self._read_curated_graph(graph_root, commit)
            if release_graph is not None:
                graph_path = graph_root / "metadata.json"
        cached_graph = self._cached_graph(slug, commit)
        if cached_graph is not None:
            cached_root, cached_path, cached_payload = cached_graph
            if self._graph_quality(cached_payload) > self._graph_quality(release_graph):
                graph_root = cached_root
                graph_path = cached_path
        verso = selected_verso(
            self.data_root, self.release_root, slug=slug,
            project_key=f"{self.project_kind}/{self.project_id}", branch=self.branch, commit=commit,
        )
        self._evidence = ReleaseEvidence(
            release_id=release.name,
            branch=self.branch,
            commit=commit,
            site_root=verso[0] if verso else site,
            verso_release_id=verso[1] if verso else release.name,
            source_root=source_root,
            project_id=self.project_id,
            project_kind=self.project_kind,
            docs_root=site / "docs" / "ReasBook",
            graph_root=graph_root,
            graph_path=graph_path,
        )
        if graph_path is not None and graph_path.name == "metadata.json":
            self._graph_payload = release_graph
        return self._evidence

    def _source_candidate_matches(
        self, release: Path, candidate: Path, expected_commit: str = "", *, require_identity: bool = False,
    ) -> bool:
        if not candidate.is_dir():
            return False
        if not expected_commit:
            return not require_identity
        release_commit = self._release_project_commit(release)
        if release_commit and release_commit != expected_commit:
            return False
        marker = release / "worktrees" / self.branch / ".reasbook-release-source.json"
        if not marker.is_file():
            return not require_identity or release_commit == expected_commit
        try:
            payload = json.loads(marker.read_text(encoding="utf-8"))
        except (OSError, ValueError, TypeError):
            return False
        marker_commit = str(payload.get("commit") or "") if isinstance(payload, dict) else ""
        if marker_commit:
            return marker_commit == expected_commit
        return not require_identity or release_commit == expected_commit

    @staticmethod
    def _safe_relative(value: str) -> PurePosixPath:
        normalized = str(value or "").replace("\\", "/").lstrip("/")
        path = PurePosixPath(normalized)
        if path.is_absolute() or not path.parts or any(part in {"", ".", ".."} for part in path.parts):
            raise ValueError("unsafe evidence path")
        if any(not _SAFE_PART.fullmatch(part) for part in path.parts):
            raise ValueError("unsafe evidence path")
        return path

    def _under(self, root: Path, relative: PurePosixPath) -> Path:
        target = (root / Path(*relative.parts)).resolve()
        if target != root and root not in target.parents:
            raise ValueError("evidence path escaped its root")
        return target

    def source_path(self, source_path: str) -> Path | None:
        evidence = self.resolve()
        if evidence is None or not evidence.source_root:
            return None
        try:
            target = self._under(evidence.source_root, self._safe_relative(source_path))
        except ValueError:
            return None
        return target if target.is_file() else None

    def lean_contract(self, item: dict[str, Any]) -> dict[str, Any]:
        """Extract the selected declaration's Lean signature and value.

        The release source is the authority here. The parser intentionally
        stops at the next top-level declaration and returns a bounded block;
        the complete file remains available in the Source evidence view.
        """

        source_path = str(item.get("sourcePath") or "")
        line_number = max(1, int(item.get("line") or 1))
        name = str(item.get("name") or item.get("declaration") or "")
        path = self.source_path(source_path)
        unavailable = {
            "available": False,
            "name": name,
            "kind": str(item.get("kind") or "statement"),
            "code": "",
            "signature": "",
            "type": "",
            "value": "",
            "sourcePath": source_path,
            "line": line_number,
        }
        if path is None:
            return unavailable
        try:
            lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        except OSError:
            return unavailable
        start = min(len(lines), line_number) - 1
        declaration = _DECLARATION_RE.match(lines[start]) if lines else None
        if declaration is None:
            for index in range(max(0, start - 10), min(len(lines), start + 3)):
                match = _DECLARATION_RE.match(lines[index])
                if match and (not name or match.group("name") == name):
                    start, declaration = index, match
                    break
        if declaration is None:
            return unavailable
        end = len(lines)
        for index in range(start + 1, len(lines)):
            if (
                _DECLARATION_RE.match(lines[index])
                or re.match(r"^\s*/--", lines[index])
                or re.match(r"^\s*/-", lines[index])
            ):
                end = index
                break
        block = "\n".join(lines[start:end]).strip()
        assignment = _declaration_assignment(block)
        signature = block if assignment < 0 else block[:assignment].rstrip()
        value = "" if assignment < 0 else block[assignment + 2 :].strip()
        depth = 0
        type_separator = -1
        for index, char in enumerate(signature):
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth = max(0, depth - 1)
            elif char == ":" and depth == 0 and not signature.startswith(":=", index):
                type_separator = index
                break
        type_text = signature[type_separator + 1 :].strip() if type_separator >= 0 else signature
        return {
            "available": True,
            "name": name or declaration.group("name"),
            "kind": declaration.group("kind"),
            "code": block,
            "signature": signature,
            "type": type_text,
            "value": value,
            "sourcePath": source_path,
            "line": start + 1,
        }

    def docs_path(self, source_path: str) -> Path | None:
        evidence = self.resolve()
        if evidence is None:
            return None
        try:
            source = self._safe_relative(source_path)
        except ValueError:
            return None
        stem = source.with_suffix("")
        candidates = (
            PurePosixPath(evidence.project_id, *stem.parts).with_suffix(".html"),
            PurePosixPath(evidence.project_id, *stem.parts, "index.html"),
            PurePosixPath(evidence.project_kind.title(), evidence.project_id, *stem.parts).with_suffix(".html"),
            PurePosixPath("ReasBook", evidence.project_kind.title(), evidence.project_id, *stem.parts).with_suffix(".html"),
            PurePosixPath(*stem.parts).with_suffix(".html"),
        )
        for candidate in candidates:
            path = self._under(evidence.docs_root, candidate)
            if path.is_file():
                return path
        return None

    def verso_path(self, source_path: str) -> Path | None:
        evidence = self.resolve()
        if evidence is None:
            return None
        try:
            source = self._safe_relative(source_path)
        except ValueError:
            return None
        stem = source.with_suffix("")
        lower = tuple(part.lower() for part in stem.parts)
        slug = str(self.book.get("slug") or "")
        collection = evidence.project_kind
        candidates: list[PurePosixPath] = []
        if stem.name.lower() == "book":
            candidates.extend((PurePosixPath(slug, "book", "index.html"), PurePosixPath(collection, slug, "index.html")))
        else:
            candidates.extend(
                (
                    PurePosixPath(slug, *lower, "index.html"),
                    PurePosixPath(collection, slug, *lower, "index.html"),
                )
            )
        for candidate in candidates:
            path = self._under(evidence.site_root, candidate)
            if path.is_file():
                return path
        return None

    def graph_payload(self) -> dict[str, Any] | None:
        if self._graph_payload is not None:
            return self._graph_payload
        evidence = self.resolve()
        if evidence is None or evidence.graph_path is None:
            return None
        self._graph_payload = (
            self._read_curated_graph(evidence.graph_root, evidence.commit)
            if evidence.graph_path.name == "metadata.json"
            else self._read_graph(evidence.graph_path)
        )
        return self._graph_payload

    def graph_for_item(self, item: dict[str, Any]) -> dict[str, Any]:
        payload = self.graph_payload()
        if not payload:
            return {
                "available": False,
                "nodes": [],
                "edges": [],
                "upstream": [],
                "downstream": [],
                "generation": None,
            }
        items = payload.get("items") if isinstance(payload.get("items"), list) else []
        source = str(item.get("sourcePath") or item.get("file") or "")
        name = str(item.get("name") or item.get("declaration") or "")
        line = int(item.get("line") or 0)
        selected = next(
            (
                value
                for value in items
                if isinstance(value, dict)
                and str(value.get("declaration") or "") == name
                and str(value.get("file") or "") == source
                and (not line or int(value.get("line") or 0) == line)
            ),
            None,
        )
        if selected is None:
            selected = next(
                (value for value in items if isinstance(value, dict) and str(value.get("declaration") or "") == name),
                None,
            )
        selected_id = str(selected.get("id")) if isinstance(selected, dict) and selected.get("id") else ""
        selected_name = str(selected.get("declaration") or "") if isinstance(selected, dict) else name
        by_id = {str(value.get("id")): value for value in items if isinstance(value, dict) and value.get("id")}
        by_name = {
            str(value.get("declaration")): value
            for value in items
            if isinstance(value, dict) and value.get("declaration")
        }

        def dependency_values(value: dict[str, Any], field: str) -> list[str]:
            dependencies = value.get(field)
            if isinstance(dependencies, list):
                return [str(dependency) for dependency in dependencies]
            if field == "dependencies":
                return list(
                    dict.fromkeys(
                        dependency_values(value, "statementDependencies")
                        + dependency_values(value, "proofDependencies")
                    )
                )
            return []

        def dependency_kinds(value: dict[str, Any], *dependency_ids: str) -> list[str]:
            identifiers = {identifier for identifier in dependency_ids if identifier}
            kinds: list[str] = []
            if identifiers.intersection(dependency_values(value, "statementDependencies")):
                kinds.append("statement")
            if identifiers.intersection(dependency_values(value, "proofDependencies")):
                kinds.append("proof")
            if not kinds and identifiers.intersection(dependency_values(value, "dependencies")):
                kinds.append("unclassified")
            return kinds

        def relation_node(value: dict[str, Any], kinds: list[str]) -> dict[str, Any]:
            return {
                "id": str(value.get("id") or ""),
                "declaration": str(value.get("declaration") or ""),
                "label": str(value.get("label") or value.get("title") or value.get("declaration") or ""),
                "title": str(value.get("title") or ""),
                "file": str(value.get("file") or ""),
                "line": int(value.get("line") or 0),
                "kinds": kinds,
            }

        upstream: list[dict[str, Any]] = []
        downstream: list[dict[str, Any]] = []
        if isinstance(selected, dict):
            for dependency in dependency_values(selected, "dependencies"):
                dependency_value = by_id.get(str(dependency)) or by_name.get(str(dependency))
                if dependency_value:
                    upstream.append(
                        relation_node(
                            dependency_value,
                            dependency_kinds(
                                selected,
                                str(dependency),
                                str(dependency_value.get("id") or ""),
                                str(dependency_value.get("declaration") or ""),
                            ),
                        )
                    )
            for value in items:
                if not isinstance(value, dict) or value is selected:
                    continue
                dependencies = set(dependency_values(value, "dependencies"))
                if selected_id in dependencies or selected_name in dependencies:
                    downstream.append(
                        relation_node(
                            value,
                            dependency_kinds(value, selected_id, selected_name),
                        )
                    )
        nodes: list[dict[str, Any]] = []
        if selected:
            nodes.append({**selected, "selected": True})
        neighbor_ids = {value["id"] for value in [*upstream, *downstream]}
        for item_id in sorted(neighbor_ids):
            value = by_id[item_id]
            if value is not selected:
                nodes.append({**value, "selected": False})
        edges: list[dict[str, Any]] = []
        known = {str(value.get("declaration")): value for value in items if isinstance(value, dict)}
        known.update({str(value.get("id")): value for value in items if isinstance(value, dict) and value.get("id")})
        node_ids = {str(value.get("id")) for value in nodes}
        for value in nodes:
            for dependency in dependency_values(value, "dependencies"):
                dep_name = str(dependency)
                if dep_name in known and str(known[dep_name].get("id")) in node_ids:
                    dependency_value = known[dep_name]
                    edges.append(
                        {
                            "source": str(dependency_value.get("id")),
                            "target": str(value.get("id")),
                            "kinds": dependency_kinds(
                                value,
                                dep_name,
                                str(dependency_value.get("id") or ""),
                                str(dependency_value.get("declaration") or ""),
                            ),
                        }
                    )
        schema_version = payload.get("schemaVersion")
        typed_dependencies = (isinstance(schema_version, int) and schema_version >= 2) or any(
            isinstance(value, dict)
            and (
                isinstance(value.get("statementDependencies"), list) or isinstance(value.get("proofDependencies"), list)
            )
            for value in items
        )
        return {
            "available": True,
            "generation": payload.get("generation"),
            "project": payload.get("project"),
            "selected": selected_id,
            "selectedDependencyEvidence": (
                str(selected.get("dependencyEvidence") or "compiled")
                if isinstance(selected, dict)
                else ""
            ),
            "nodes": nodes,
            "edges": edges,
            "upstream": upstream,
            "downstream": downstream,
            "typedDependencies": typed_dependencies,
            "totalNodes": len(items),
            "totalEdges": sum(
                len(dependency_values(value, "dependencies")) for value in items if isinstance(value, dict)
            ),
        }

    def manifest(self, base_url: str, item: dict[str, Any] | None = None) -> dict[str, Any]:
        evidence = self.resolve()
        if evidence is None:
            return {"available": False, "branch": self.branch, "commit": self.commit}
        result: dict[str, Any] = {
            "available": True,
            "releaseId": evidence.release_id,
            "branch": evidence.branch,
            "commit": evidence.commit,
            "source": {"available": evidence.source_available},
            "docs": {"available": evidence.docs_available},
            "verso": {"available": evidence.site_available,
                      "releaseId": getattr(evidence, "verso_release_id", "") or evidence.release_id},
            "graphs": {"available": evidence.graph_available},
            "graph": {"available": evidence.graph_available},
        }
        if item is not None:
            source_path = str(item.get("sourcePath") or "")
            docs = self.docs_path(source_path)
            verso = self.verso_path(source_path)
            result["source"]["available"] = self.source_path(source_path) is not None
            result["source"]["path"] = source_path
            result["docs"]["available"] = docs is not None
            result["verso"]["available"] = verso is not None
            result["docs"]["url"] = (
                f"{base_url}/evidence/docs/{self._relative_docs(docs, evidence).as_posix()}" if docs else ""
            )
            result["verso"]["url"] = (
                f"{base_url}/evidence/verso/{self._relative_site(verso, evidence).as_posix()}" if verso else ""
            )
            if evidence.graph_available:
                result["graph"]["url"] = f"{base_url}/evidence/graph/index.html"
        return result

    @staticmethod
    def _relative_docs(path: Path | None, evidence: ReleaseEvidence) -> PurePosixPath:
        return PurePosixPath(path.relative_to(evidence.docs_root).as_posix()) if path else PurePosixPath("")

    @staticmethod
    def _relative_site(path: Path | None, evidence: ReleaseEvidence) -> PurePosixPath:
        return PurePosixPath(path.relative_to(evidence.site_root).as_posix()) if path else PurePosixPath("")

    def evidence_file(self, kind: str, path: str) -> tuple[Path, ReleaseEvidence] | None:
        evidence = self.resolve()
        if evidence is None or kind not in {"docs", "documentation", "verso", "graph"}:
            return None
        root = evidence.docs_root if kind in {"docs", "documentation"} else evidence.site_root
        if kind == "graph":
            root = evidence.graph_root
            # Both generic and safely parsed curated data use the same renderer.
            # Keep original assets available for inspecting the immutable release.
            original = path.startswith("original/")
            if original:
                path = path.removeprefix("original/")
            payload = self.graph_payload() or {}
            generation = payload.get("generation") or {}
            if (
                not original
                and payload.get("schemaVersion") in {1, 2}
                and generation.get("mode") in {"lean-environment", "lean-environment-partial", "source-fallback", "curated", "curated-static"}
                and path in {"index.html", "app.js", "styles.css", "vendor/viz-global.js"}
            ):
                asset = GRAPH_ASSETS / path
                return (asset, evidence) if asset.is_file() else None
        try:
            target = self._under(root, self._safe_relative(path))
        except ValueError:
            return None
        if target.is_dir() and (target / "index.html").is_file():
            target = target / "index.html"
        return (target, evidence) if target.is_file() else None


def rewrite_html_for_proxy(
    text: str,
    *,
    kind: str,
    prefix: str,
    branch: str = "",
    docs_prefix: str = "",
    relative_base: str = "",
    project_id: str = "",
    project_kind: str = "books",
) -> str:
    """Rewrite release-root links so an iframe can navigate under the API route."""

    if kind == "verso":
        # A relative evidence root is essential when an outer ingress owns an
        # unknown browser-visible prefix (for example /proxy/3000/ReasBook).
        # Root-relative /api links would escape that ingress after the iframe
        # loads even though the outer reviewer itself rendered successfully.
        site_prefix = "" if relative_base else f"{prefix.rstrip('/')}/"
        effective_docs_prefix = "../documentation/" if relative_base and docs_prefix else f"{docs_prefix.rstrip('/')}/"
        base_href = relative_base or site_prefix
        text = re.sub(
            r'<base\s+href="[^"]*"\s*/?>',
            f'<base href="{base_href}" />',
            text,
            count=1,
            flags=re.IGNORECASE,
        )
        common_prefix = "" if relative_base else prefix.rsplit("/verso", 1)[0] + "/"
        text = re.sub(
            r'window\.__versoSiteRoot\s*=\s*"[^"]*"',
            f'window.__versoSiteRoot="{common_prefix}"',
            text,
            count=1,
        )
        if branch:
            if docs_prefix:
                text = text.replace(
                    f"/ReasBook/versions/{branch}/docs/ReasBook/",
                    effective_docs_prefix,
                )
            text = text.replace(f"/ReasBook/versions/{branch}/", site_prefix)
        if docs_prefix:
            text = text.replace("/ReasBook/versions/docs/ReasBook/", effective_docs_prefix)
        text = text.replace("/ReasBook/versions/", site_prefix)
        if docs_prefix:
            # Doc-gen's /find page loads ./find.js and therefore needs the
            # directory form. Without the slash, the browser asks for
            # <documentation>/find.js instead of <documentation>/find/find.js.
            find_prefix = re.escape(effective_docs_prefix.rstrip("/"))
            text = re.sub(
                rf"({find_prefix}/find)(?=[?#\"'\s>])",
                r"\1/",
                text,
            )
    elif kind == "docs" and project_id:
        source_dir = "Papers" if project_kind == "papers" else "Books"
        marker = f"/ReasBook/{source_dir}/{project_id}/"
        marker_json = json.dumps(marker)
        jump_script = f"""
<script>
(function () {{
  const sourceMarker = {marker_json};
  document.addEventListener("click", function (event) {{
    if (event.defaultPrevented || event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
    const anchor = event.target && event.target.closest ? event.target.closest("a[href]") : null;
    if (!anchor) return;
    let url;
    try {{ url = new URL(anchor.href, window.location.href); }} catch (_) {{ return; }}
    const index = url.pathname.indexOf(sourceMarker);
    const line = (url.hash || "").match(/^#L(\\d+)/i);
    if (index < 0 || !line || window.parent === window) return;
    event.preventDefault();
    window.parent.postMessage({{
      type: "reasbook-source-jump",
      sourcePath: decodeURIComponent(url.pathname.slice(index + sourceMarker.length)),
      line: Number(line[1])
    }}, "*");
  }}, true);
}})();
</script>
"""
        insertion = re.search(r"</body>", text, flags=re.IGNORECASE)
        if insertion:
            text = text[: insertion.start()] + jump_script + text[insertion.start() :]
        else:
            text += jump_script
    return text
