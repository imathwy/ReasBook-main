from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from verso_build_sdk.literate import LiterateCacheError, LiterateCacheIdentity
from verso_build_sdk.literate_fragments import (
    LiterateFragmentIdentity,
    assemble_fragments,
    partition_modules,
    publish_fragment,
)


def ordered_digest(modules: tuple[str, ...]) -> str:
    encoded = json.dumps(list(modules), separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


class LiterateFragmentTests(unittest.TestCase):
    modules = (
        "Books.Convex.A",
        "Books.Convex.B",
        "Books.Convex.C",
        "Books.Convex.D",
        "Books.Convex.E",
    )

    def identity(self) -> LiterateCacheIdentity:
        return LiterateCacheIdentity(
            branch="v4.26.0",
            commit="a" * 40,
            lake_manifest_sha256="b" * 64,
            toolchain="leanprover/lean4:v4.26.0",
            architecture="x86_64",
            modules_sha256=ordered_digest(self.modules),
            source_tree_sha256="c" * 64,
            tooling_sha256="d" * 64,
        )

    @staticmethod
    def write_artifact(root: Path, module: str) -> None:
        output = root / Path(*module.split(".")).with_suffix(".json")
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps([{"module": module}]), encoding="utf-8")
        Path(f"{output}.hash").write_text("0123456789abcdef", encoding="ascii")
        Path(f"{output}.trace").write_text(
            json.dumps({"module": module}), encoding="utf-8"
        )

    def publish_all(self, root: Path) -> tuple[Path, ...]:
        source = root / "private-lake" / "build" / "literate"
        for module in self.modules:
            self.write_artifact(source, module)
        batches = partition_modules(self.modules, targets_per_job=3)
        fragments = []
        for index, batch in enumerate(batches):
            destination = root / "fragments" / f"batch-{index:03d}"
            publish_fragment(
                source,
                destination,
                LiterateFragmentIdentity(
                    "site-fixture",
                    "sha256:" + "e" * 64,
                    "books/Convex",
                    self.identity(),
                    index,
                    len(batches),
                    batch,
                ),
            )
            fragments.append(destination)
        return tuple(fragments)

    def test_partition_is_deterministic_and_exact(self) -> None:
        self.assertEqual(
            partition_modules(self.modules, targets_per_job=2),
            (self.modules[:2], self.modules[2:4], self.modules[4:]),
        )
        for invalid in (0, 257, True):
            with self.subTest(invalid=invalid), self.assertRaises(LiterateCacheError):
                partition_modules(self.modules, targets_per_job=invalid)

    def test_publish_and_barrier_create_a_normal_complete_cache(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            fragments = self.publish_all(root)
            destination = root / "assembled" / "build" / "literate"
            marker = assemble_fragments(
                tuple(reversed(fragments)),
                destination,
                release_id="site-fixture",
                spec_digest="sha256:" + "e" * 64,
                project_key="books/Convex",
                parent_identity=self.identity(),
                modules=self.modules,
            )

            value = json.loads(marker.read_text(encoding="utf-8"))
            self.assertEqual(value["identity"], self.identity().public_dict())
            self.assertEqual(
                [item["module"] for item in value["artifacts"]], list(self.modules)
            )
            for module in self.modules:
                output = destination / Path(*module.split(".")).with_suffix(".json")
                self.assertTrue(output.is_file())
                self.assertTrue(Path(f"{output}.hash").is_file())
                self.assertTrue(Path(f"{output}.trace").is_file())

            # Both transport publication and the barrier are retry-safe.
            first_manifest = json.loads(
                (fragments[0] / "fragment.json").read_text(encoding="utf-8")
            )
            first_identity = first_manifest["identity"]
            batch_identity = LiterateFragmentIdentity(
                first_identity["release_id"],
                first_identity["spec_digest"],
                first_identity["project_key"],
                self.identity(),
                first_identity["batch_index"],
                first_identity["batch_count"],
                tuple(first_identity["modules"]),
            )
            self.assertEqual(
                publish_fragment(
                    root / "private-lake" / "build" / "literate",
                    fragments[0],
                    batch_identity,
                ),
                fragments[0] / "fragment.json",
            )
            self.assertEqual(
                assemble_fragments(
                    fragments,
                    destination,
                    release_id="site-fixture",
                    spec_digest="sha256:" + "e" * 64,
                    project_key="books/Convex",
                    parent_identity=self.identity(),
                    modules=self.modules,
                ),
                marker,
            )

    def test_incomplete_barrier_fails_without_touching_destination(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            fragments = self.publish_all(root)
            destination = root / "assembled" / "build" / "literate"
            destination.mkdir(parents=True)
            sentinel = destination / "sentinel"
            sentinel.write_text("old", encoding="utf-8")

            with self.assertRaises(LiterateCacheError):
                assemble_fragments(
                    fragments[:1],
                    destination,
                    release_id="site-fixture",
                    spec_digest="sha256:" + "e" * 64,
                    project_key="books/Convex",
                    parent_identity=self.identity(),
                    modules=self.modules,
                )
            self.assertEqual(sentinel.read_text(encoding="utf-8"), "old")

    def test_tampered_artifact_is_rejected_before_merge(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            fragments = self.publish_all(root)
            output = fragments[0] / "Books" / "Convex" / "A.json"
            output.write_text("[]", encoding="utf-8")

            with self.assertRaisesRegex(LiterateCacheError, "digest mismatch"):
                assemble_fragments(
                    fragments,
                    root / "assembled" / "build" / "literate",
                    release_id="site-fixture",
                    spec_digest="sha256:" + "e" * 64,
                    project_key="books/Convex",
                    parent_identity=self.identity(),
                    modules=self.modules,
                )


if __name__ == "__main__":
    unittest.main()
