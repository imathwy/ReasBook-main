"""Catalog subject vocabulary and the non-collapsible reading workspace contract."""

import json
from pathlib import Path
import re
import unittest


DOCS = Path(__file__).resolve().parents[1] / "docs"


class CatalogUIContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.script = (DOCS / "app.js").read_text()
        cls.html = (DOCS / "index.html").read_text()
        cls.styles = (DOCS / "styles.css").read_text()

    def constant(self, name):
        match = re.search(rf"const {name} = (\{{.*?\n  \}});", self.script, re.S)
        self.assertIsNotNone(match, name)
        return json.loads(match.group(1))

    def test_explicit_cross_subject_mapping_and_general_fallback(self):
        subjects = self.constant("SUBJECT_LABELS")
        books = self.constant("BOOK_SUBJECTS")
        self.assertEqual(len(books), 17)
        self.assertNotIn("book", subjects)
        self.assertNotIn("paper", subjects)
        for slug, values in books.items():
            with self.subTest(slug=slug):
                self.assertTrue(values)
                self.assertTrue(set(values) <= subjects.keys())
                self.assertEqual(len(values), len(set(values)))
        self.assertEqual(set(books["convexanalysis_rockafellar_1970"]), {"analysis", "optimization"})
        self.assertEqual(set(books["onsomelocalrings_maassaran_2025"]), {"algebra"})
        self.assertIn('BOOK_SUBJECTS[book.slug] || ["general"]', self.script)
        self.assertIn("subjects.some((subject) => state.subjectFilters.has(subject))", self.script)

    def test_subject_controls_are_labelled_and_count_survives_heading_removal(self):
        self.assertIn('id="subjectOptions"', self.html)
        self.assertIn('<legend class="sr-only">Mathematical subjects</legend>', self.html)
        self.assertIn('type="checkbox"', self.script)
        self.assertIn('id="bookCount" class="catalog-result-count" role="status"', self.html)
        self.assertNotIn("<h1>Books &amp; Papers</h1>", self.html)

    def test_evidence_cannot_be_collapsed_by_buttons_or_stale_preferences(self):
        for identifier in ("toggleCanvas", "canvasPanelToggle", "canvasRailToggle"):
            self.assertNotIn(f'id="{identifier}"', self.html)
            self.assertNotIn(f"refs.{identifier}", self.script)
        self.assertNotIn("data-canvas-collapsed", self.styles)
        self.assertIn('localStorage.removeItem(panelPreferenceKey("canvas"))', self.script)
        for panel in ("catalog", "queue", "review"):
            self.assertIn(f'id="{panel}Resize"', self.html)
        self.assertIn(".brand-block, .workspace-toolbar", self.styles)
        self.assertIn("--workspace-header-height", self.styles)

    def test_book_status_is_below_evidence_tabs_not_in_queue(self):
        queue_start = self.html.index('id="evidencePanel"')
        canvas_start = self.html.index('id="canvasPanel"')
        status = self.html.index('id="bookOverview"')
        tabs_end = self.html.index('</header>', canvas_start)
        graph = self.html.index('id="graphView"')
        self.assertNotIn('id="bookOverview"', self.html[queue_start:canvas_start])
        self.assertEqual(self.html.count('id="bookOverview"'), 1)
        self.assertLess(tabs_end, status)
        self.assertLess(status, graph)
        self.assertRegex(self.styles, r'\.book-overview-row\s*\{[^}]*flex-wrap: wrap')
        self.assertNotIn('[data-queue-collapsed="true"] .book-overview', self.styles)


if __name__ == "__main__":
    unittest.main()
