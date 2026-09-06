"""Persistent per-user reviews and append-only audit history.

Independent of HTTP and catalogs; compatible with existing SQLite databases.
"""

from __future__ import annotations

from contextlib import closing
from dataclasses import dataclass
from pathlib import Path
import sqlite3
from typing import Any

STATUS_VALUES = {"unreviewed", "accepted", "mismatch", "other"}
MAX_COMMENT_CHARS = 20_000
MAX_CLIENT_ID_CHARS = 120


class ReviewConflict(Exception):
    def __init__(self, current: dict[str, Any]):
        super().__init__("review conflict")
        self.current = current


@dataclass(frozen=True)
class Actor:
    subject: str
    display_name: str
    email: str | None
    role: str = "reviewer"


class ReviewStore:
    """SQLite store shared by all books, with book slug in every key."""

    def __init__(self, path: Path):
        self.path = path
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._init_db()

    def connect(self) -> sqlite3.Connection:
        conn = sqlite3.connect(self.path, timeout=30)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA busy_timeout=30000")
        return conn

    def _init_db(self) -> None:
        with closing(self.connect()) as conn, conn:
            conn.executescript(
                """
                CREATE TABLE IF NOT EXISTS users (
                    actor_id TEXT PRIMARY KEY,
                    email TEXT,
                    display_name TEXT NOT NULL,
                    role TEXT NOT NULL DEFAULT 'reviewer',
                    first_seen_at TEXT NOT NULL,
                    last_seen_at TEXT NOT NULL
                );

                CREATE TABLE IF NOT EXISTS current_reviews (
                    book_slug TEXT NOT NULL,
                    item_key TEXT NOT NULL,
                    status TEXT NOT NULL,
                    comment TEXT NOT NULL,
                    reviewer TEXT NOT NULL,
                    actor_id TEXT NOT NULL,
                    actor_role TEXT NOT NULL,
                    client_id TEXT NOT NULL,
                    updated_at TEXT NOT NULL,
                    revision INTEGER NOT NULL,
                    PRIMARY KEY (book_slug, item_key, actor_id)
                );

                CREATE TABLE IF NOT EXISTS review_events (
                    revision INTEGER PRIMARY KEY AUTOINCREMENT,
                    book_slug TEXT NOT NULL,
                    item_key TEXT NOT NULL,
                    status TEXT NOT NULL,
                    comment TEXT NOT NULL,
                    reviewer TEXT NOT NULL,
                    actor_id TEXT NOT NULL,
                    actor_role TEXT NOT NULL,
                    client_id TEXT NOT NULL,
                    previous_status TEXT,
                    previous_comment TEXT,
                    previous_revision INTEGER,
                    remote_addr TEXT,
                    user_agent TEXT,
                    created_at TEXT NOT NULL
                );

                CREATE INDEX IF NOT EXISTS idx_current_reviews_book
                    ON current_reviews(book_slug, revision);
                CREATE INDEX IF NOT EXISTS idx_review_events_book
                    ON review_events(book_slug, revision);
                CREATE INDEX IF NOT EXISTS idx_review_events_item
                    ON review_events(book_slug, item_key, revision);
                """
            )

    @staticmethod
    def _row(row: sqlite3.Row) -> dict[str, Any]:
        return {
            "bookSlug": row["book_slug"],
            "itemKey": row["item_key"],
            "status": row["status"],
            "comment": row["comment"],
            "reviewer": row["reviewer"],
            "actorId": row["actor_id"],
            "actorRole": row["actor_role"],
            "clientId": row["client_id"],
            "updatedAt": row["updated_at"],
            "revision": int(row["revision"]),
        }

    def _max_revision(self, conn: sqlite3.Connection, book_slug: str | None = None) -> int:
        if book_slug is None:
            row = conn.execute("SELECT COALESCE(MAX(revision), 0) AS value FROM review_events").fetchone()
        else:
            row = conn.execute(
                "SELECT COALESCE(MAX(revision), 0) AS value FROM review_events WHERE book_slug = ?",
                (book_slug,),
            ).fetchone()
        return int(row["value"] if row else 0)

    def upsert_user(self, actor: Actor) -> None:
        timestamp = _now_iso()
        with closing(self.connect()) as conn, conn:
            existing = conn.execute("SELECT role FROM users WHERE actor_id = ?", (actor.subject,)).fetchone()
            role = str(existing["role"]) if existing and existing["role"] in {"reviewer", "admin"} else actor.role
            conn.execute(
                """INSERT INTO users(actor_id, email, display_name, role, first_seen_at, last_seen_at)
                   VALUES (?, ?, ?, ?, ?, ?)
                   ON CONFLICT(actor_id) DO UPDATE SET
                     email = excluded.email,
                     display_name = excluded.display_name,
                     last_seen_at = excluded.last_seen_at""",
                (actor.subject, actor.email, actor.display_name[:120], role, timestamp, timestamp),
            )

    def role_for(self, subject: str) -> str:
        with closing(self.connect()) as conn:
            row = conn.execute("SELECT role FROM users WHERE actor_id = ?", (subject,)).fetchone()
        return str(row["role"]) if row and row["role"] in {"reviewer", "admin"} else "reviewer"

    def list_reviews(self, book_slug: str, since: int | None = None) -> dict[str, Any]:
        with closing(self.connect()) as conn:
            if since is None:
                rows = conn.execute(
                    "SELECT * FROM current_reviews WHERE book_slug = ? ORDER BY item_key, actor_id",
                    (book_slug,),
                ).fetchall()
            else:
                rows = conn.execute(
                    "SELECT * FROM current_reviews WHERE book_slug = ? AND revision > ? ORDER BY revision",
                    (book_slug, since),
                ).fetchall()
            return {
                "bookSlug": book_slug,
                "reviews": [self._row(row) for row in rows],
                "revision": self._max_revision(conn, book_slug),
            }

    def list_history(self, book_slug: str, item_key: str) -> list[dict[str, Any]]:
        """Public history without private transport metadata."""

        with closing(self.connect()) as conn:
            rows = conn.execute(
                """SELECT * FROM review_events
                   WHERE book_slug = ? AND item_key = ? ORDER BY revision DESC""",
                (book_slug, item_key),
            ).fetchall()
        return [
            {
                "revision": int(row["revision"]),
                "bookSlug": row["book_slug"],
                "itemKey": row["item_key"],
                "status": row["status"],
                "comment": row["comment"],
                "reviewer": row["reviewer"],
                "actorId": row["actor_id"],
                "actorRole": row["actor_role"],
                "clientId": row["client_id"],
                "previousStatus": row["previous_status"],
                "previousComment": row["previous_comment"],
                "previousRevision": row["previous_revision"],
                "createdAt": row["created_at"],
            }
            for row in rows
        ]

    def list_events(self, book_slug: str | None = None) -> list[dict[str, Any]]:
        """Full audit records for authenticated administrator export only."""

        with closing(self.connect()) as conn:
            if book_slug:
                rows = conn.execute("SELECT * FROM review_events WHERE book_slug = ? ORDER BY revision", (book_slug,)).fetchall()
            else:
                rows = conn.execute("SELECT * FROM review_events ORDER BY revision").fetchall()
        return [dict(row) for row in rows]

    def save_review(
        self,
        book_slug: str,
        item_key: str,
        payload: dict[str, Any],
        actor: Actor,
        *,
        remote_addr: str = "",
        user_agent: str = "",
    ) -> dict[str, Any]:
        if not isinstance(payload, dict):
            raise ValueError("request body must be a JSON object")
        review_status = str(payload.get("status", "") or "")
        if review_status not in STATUS_VALUES:
            raise ValueError("status must be one of: unreviewed, accepted, mismatch, other")
        comment = str(payload.get("comment", "") or "")
        if len(comment) > MAX_COMMENT_CHARS:
            raise ValueError(f"comment is too long; max {MAX_COMMENT_CHARS} characters")
        client_id = str(payload.get("clientId", "") or "").strip()
        if not client_id or len(client_id) > MAX_CLIENT_ID_CHARS:
            raise ValueError("clientId is required")
        base_revision = payload.get("baseRevision", 0)
        # A revision is a JSON integer, not a coercible float, boolean, or
        # string. Coercion can turn a stale edit into a matching revision.
        if type(base_revision) is not int:
            raise ValueError("baseRevision must be an integer")
        if base_revision < 0:
            raise ValueError("baseRevision must not be negative")

        now = _now_iso()
        reviewer = actor.display_name or actor.subject
        with closing(self.connect()) as conn, conn:
            conn.execute("BEGIN IMMEDIATE")
            current = conn.execute(
                """SELECT * FROM current_reviews
                   WHERE book_slug = ? AND item_key = ? AND actor_id = ?""",
                (book_slug, item_key, actor.subject),
            ).fetchone()
            current_revision = int(current["revision"]) if current else 0
            if base_revision != current_revision:
                raise ReviewConflict(self._row(current) if current else _default_review(book_slug, item_key))
            conn.execute(
                """INSERT INTO review_events(
                     book_slug, item_key, status, comment, reviewer, actor_id,
                     actor_role, client_id, previous_status, previous_comment,
                     previous_revision, remote_addr, user_agent, created_at
                   ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
                (
                    book_slug,
                    item_key,
                    review_status,
                    comment,
                    reviewer,
                    actor.subject,
                    actor.role,
                    client_id,
                    current["status"] if current else None,
                    current["comment"] if current else None,
                    current_revision if current else None,
                    remote_addr[:120],
                    user_agent[:512],
                    now,
                ),
            )
            revision = int(conn.execute("SELECT last_insert_rowid()").fetchone()[0])
            conn.execute(
                """INSERT INTO current_reviews(
                     book_slug, item_key, status, comment, reviewer, actor_id,
                     actor_role, client_id, updated_at, revision
                   ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                   ON CONFLICT(book_slug, item_key, actor_id) DO UPDATE SET
                     status = excluded.status,
                     comment = excluded.comment,
                     reviewer = excluded.reviewer,
                     actor_role = excluded.actor_role,
                     client_id = excluded.client_id,
                     updated_at = excluded.updated_at,
                     revision = excluded.revision""",
                (
                    book_slug,
                    item_key,
                    review_status,
                    comment,
                    reviewer,
                    actor.subject,
                    actor.role,
                    client_id,
                    now,
                    revision,
                ),
            )
            row = conn.execute(
                "SELECT * FROM current_reviews WHERE book_slug = ? AND item_key = ? AND actor_id = ?",
                (book_slug, item_key, actor.subject),
            ).fetchone()
            return self._row(row)


def _default_review(book_slug: str, item_key: str) -> dict[str, Any]:
    return {
        "bookSlug": book_slug,
        "itemKey": item_key,
        "status": "unreviewed",
        "comment": "",
        "reviewer": "",
        "actorId": "",
        "actorRole": "",
        "clientId": "",
        "updatedAt": "",
        "revision": 0,
    }


def _now_iso() -> str:
    from datetime import datetime, timezone

    return datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")
