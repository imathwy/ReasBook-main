"""Storage behavior without importing or starting the web application."""

from pathlib import Path
import tempfile
import unittest

from storage import Actor, ReviewConflict, ReviewStore


class ReviewStoreTests(unittest.TestCase):
    def test_persists_per_book_review_and_detects_conflict(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            store = ReviewStore(Path(temp_dir) / "reviews.sqlite3")
            actor = Actor("user-1", "Reviewer One", "one@example.test")
            saved = store.save_review(
                "analysis2_tao_2022",
                "Analysis2.chapter1.theorem1",
                {
                    "status": "accepted",
                    "comment": "Matches the source statement.",
                    "clientId": "test-client",
                    "baseRevision": 0,
                },
                actor,
            )

            self.assertEqual(saved["revision"], 1)
            self.assertEqual(store.list_reviews("analysis2_tao_2022")["reviews"], [saved])
            self.assertEqual(store.list_reviews("convexanalysis_rockafellar_1970")["reviews"], [])
            with self.assertRaises(ReviewConflict):
                store.save_review(
                    "analysis2_tao_2022",
                    "Analysis2.chapter1.theorem1",
                    {
                        "status": "mismatch",
                        "comment": "Stale edit",
                        "clientId": "second-client",
                        "baseRevision": 0,
                    },
                    actor,
                )

            # Opening the same database exercises compatibility and durability,
            # including rollback of the failed optimistic update above.
            reopened = ReviewStore(Path(temp_dir) / "reviews.sqlite3")
            self.assertEqual(reopened.list_reviews("analysis2_tao_2022")["reviews"], [saved])
            self.assertEqual(len(reopened.list_events()), 1)
            changed = reopened.save_review(
                "analysis2_tao_2022",
                "Analysis2.chapter1.theorem1",
                {"status": "other", "comment": "Rechecked", "clientId": "client", "baseRevision": 1},
                actor,
            )
            self.assertEqual(changed["revision"], 2)
            event = reopened.list_events()[-1]
            self.assertEqual(event["previous_comment"], saved["comment"])
            self.assertEqual(event["previous_revision"], 1)

    def test_different_reviewers_have_independent_revision_checks(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            store = ReviewStore(Path(temp_dir) / "reviews.sqlite3")
            payload = {"status": "accepted", "comment": "", "clientId": "client", "baseRevision": 0}
            for subject in ("alice", "bob"):
                store.save_review("book", "theorem", payload, Actor(subject, subject, None))
            self.assertEqual(len(store.list_reviews("book")["reviews"]), 2)
            self.assertEqual(store.list_reviews("book")["revision"], 2)

    def test_malformed_revisions_never_write_events(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            store = ReviewStore(Path(temp_dir) / "reviews.sqlite3")
            actor = Actor("alice", "Alice", None)
            for revision in (True, False, None, [], {}, "0", 0.9, float("inf"), -1):
                with self.subTest(revision=revision), self.assertRaises(ValueError):
                    store.save_review(
                        "book", "theorem",
                        {"status": "accepted", "comment": "", "clientId": "client", "baseRevision": revision},
                        actor,
                    )
            self.assertEqual(store.list_events(), [])
