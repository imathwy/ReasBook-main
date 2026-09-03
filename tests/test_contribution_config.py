from __future__ import annotations

import json
from pathlib import Path
import re
import unittest

import yaml


ROOT = Path(__file__).resolve().parents[1]


class ContributionConfigTests(unittest.TestCase):
    def test_book_schema_accepts_every_registered_stable_toolchain(self) -> None:
        registry = yaml.safe_load(
            (ROOT / "config" / "toolchains.yml").read_text(encoding="utf-8")
        )
        schema = json.loads(
            (ROOT / "config" / "schemas" / "book.schema.json").read_text(
                encoding="utf-8"
            )
        )

        for item in registry["branches"]:
            version = item["version"]
            values = {
                "toolchain": f"leanprover/lean4:{version}",
                "mathlib": version,
                "branch": version,
            }
            for field, value in values.items():
                with self.subTest(version=version, field=field):
                    pattern = schema["properties"][field]["pattern"]
                    self.assertIsNotNone(re.fullmatch(pattern, value))


if __name__ == "__main__":
    unittest.main()
