#!/usr/bin/env python3
"""Focused regression tests for theorem-map selection and dependency contraction."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import catalog
import generate_all


class TheoremMapTests(unittest.TestCase):
    def test_label_normalization(self) -> None:
        self.assertEqual(
            generate_all.normalize_label("theorem", "A.2_3"),
            ("Theorem A.2.3", "theorem-a-2-3", "Theorem"),
        )

    def test_hyphenated_literature_label(self) -> None:
        match = generate_all.LABEL_RE.match(
            "Corollary 1-11-21: a subgroup consequence."
        )
        self.assertIsNotNone(match)
        self.assertEqual(match.group("number"), "1-11-21")

    def test_contracts_project_helpers(self) -> None:
        raw = {
            "Article.main": {"dependencies": ["Internal.bridge"]},
            "Internal.bridge": {"dependencies": ["Article.base", "Mathlib.fact"]},
            "Article.base": {"dependencies": []},
        }
        selected = {
            "Article.main": "theorem-2-2",
            "Article.base": "lemma-2-1",
        }
        self.assertEqual(
            generate_all.nearest_article_dependencies(
                "Article.main", raw, selected
            ),
            ["lemma-2-1"],
        )

    def test_generic_projects_are_opt_in(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            curated_root = root / "curated"
            generated_root = root / "generated"
            (curated_root / "theorem-map").mkdir(parents=True)
            (curated_root / "theorem-map" / "index.html").write_text(
                "<!doctype html>", encoding="utf-8"
            )
            curated = generate_all.Project(
                kind="papers",
                kind_dir="Papers",
                leaf="Paper",
                project_id="Curated",
                root=curated_root,
                root_module=None,
            )
            generated = generate_all.Project(
                kind="books",
                kind_dir="Books",
                leaf="Book",
                project_id="Generated",
                root=generated_root,
                root_module="Generated.Book",
            )
            self.assertEqual(generate_all.generic_projects([curated, generated], False), [])
            self.assertEqual(
                generate_all.generic_projects([curated, generated], True), [generated]
            )

    def test_merged_catalog_reads_metadata(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            site_root = Path(temp)
            map_root = site_root / "theorem-maps" / "papers" / "sample"
            map_root.mkdir(parents=True)
            (map_root / "index.html").write_text("<!doctype html>", encoding="utf-8")
            (map_root / "metadata.json").write_text(
                json.dumps(
                    {
                        "project": {
                            "id": "Sample",
                            "title": "Sample paper",
                            "branch": "v4.32.2",
                        },
                        "nodes": 7,
                        "edges": 9,
                    }
                ),
                encoding="utf-8",
            )
            output = catalog.write_catalog(site_root)
            rendered = output.read_text(encoding="utf-8")
            self.assertIn("Sample paper", rendered)
            self.assertIn("v4.32.2", rendered)
            self.assertIn("<td>7</td><td>9</td>", rendered)


if __name__ == "__main__":
    unittest.main()
