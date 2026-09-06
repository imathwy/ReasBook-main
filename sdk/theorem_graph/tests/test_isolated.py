from dataclasses import replace
import json
import os
from pathlib import Path
import subprocess
import tempfile
from threading import Barrier
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from theorem_graph_sdk import Project, build_data, merge_compiled_graphs
from theorem_graph_sdk.errors import ExtractionError
from theorem_graph_sdk.isolated import available_modules, extract_available


class IsolatedExtractionTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / "source"
        self.source.mkdir()
        self.compiled = self.root / "compiled"
        (self.compiled / "Demo").mkdir(parents=True)
        self.project = Project(
            "books", "Books", "Book", "Demo", self.source, "Demo.Book"
        )

    def graph(self, raw):
        return build_data(
            self.project, raw, "https://example.invalid/repo", "v4.30.0", "commit"
        )

    @staticmethod
    def declaration(name, module, label, deps):
        return {
            "name": name,
            "moduleName": module,
            "line": 1,
            "kind": "theorem",
            "docString": label,
            "statementDependencies": [],
            "proofDependencies": deps,
            "dependencies": deps,
        }

    def test_same_named_helpers_cannot_contaminate_other_environments(self):
        for name in ("A", "B"):
            (self.source / f"{name}.lean").write_text("-- source\n")
        a = [
            self.declaration("a", "Demo.A", "Lemma 1.1: A base.", []),
            self.declaration("helper", "Demo.A", "", ["a"]),
            self.declaration("mainA", "Demo.A", "Theorem 1.2: A result.", ["helper"]),
        ]
        b = [
            self.declaration("b", "Demo.B", "Lemma 2.1: B base.", []),
            self.declaration("helper", "Demo.B", "", ["b"]),
            self.declaration("mainB", "Demo.B", "Theorem 2.2: B result.", ["helper"]),
        ]
        ga, gb = self.graph(a), self.graph(b)
        source = {**ga, "items": ga["items"] + gb["items"]}
        merged = merge_compiled_graphs([ga, gb], source)
        items = {item["id"]: item for item in merged["items"]}
        self.assertEqual(items["theorem-1-2"]["proofDependencies"], ["lemma-1-1"])
        self.assertEqual(items["theorem-2-2"]["proofDependencies"], ["lemma-2-1"])
        gb["project"]["commit"] = "other"
        with self.assertRaises(ExtractionError):
            merge_compiled_graphs([ga, gb], source)

    def test_inventory_and_collision_bisection_never_modify_input_trees(self):
        for name in ("A", "B", "Missing"):
            (self.source / f"{name}.lean").write_text("-- source\n")
        for name in ("A", "B"):
            (self.compiled / "Demo" / f"{name}.olean").write_bytes(b"compiled")
        self.assertEqual(
            available_modules(self.project, self.compiled, "Demo"),
            (["Demo.A", "Demo.B"], ["Demo.Missing"]),
        )
        lean_bin = self.root / "toolchain/bin/lean"
        lean_bin.parent.mkdir(parents=True)
        lean_bin.write_text("fake lean\n")
        before = {
            path: path.read_bytes()
            for directory in (self.source, self.compiled)
            for path in directory.rglob("*")
            if path.is_file()
        }

        def run(command):
            config, raw = (Path(part) for part in command.argv[-2:])
            modules = json.loads(config.read_text())["projects"][0]["rootModules"]
            self.assertEqual(command.argv[1:5], ("-j", "1", "-M", "4096"))
            self.assertIn(
                command.cwd.parent, {self.root / "output", self.root / "parallel"}
            )
            if len(modules) > 1:
                return SimpleNamespace(returncode=1)
            number = 1 if modules[0] == "Demo.A" else 2
            raw.write_text(
                json.dumps(
                    [
                        {
                            "id": "Demo",
                            "declarations": [
                                self.declaration(
                                    f"result{number}",
                                    modules[0],
                                    f"Lemma {number}.1: result.",
                                    [],
                                )
                            ],
                        }
                    ]
                )
            )
            return SimpleNamespace(returncode=0)

        with patch("theorem_graph_sdk.isolated.CommandRunner") as runner:
            runner.return_value.run.side_effect = run
            report = extract_available(
                self.project,
                compiled_root=self.compiled,
                module_prefix="Demo",
                search_paths=[],
                lean_bin=lean_bin,
                output=self.root / "output",
                branch="v4.30.0",
                commit="commit",
                repository="repo",
            )
        self.assertEqual(len(report["attempts"]), 3)
        self.assertEqual(report["completedModules"], ["Demo.A", "Demo.B"])
        self.assertEqual(report["missingModules"], ["Demo.Missing"])
        graph = json.loads((self.root / "output/map/data.json").read_text())
        self.assertEqual(graph["generation"]["dependencyCoverage"], "partial")
        self.assertEqual(
            before,
            {
                path: path.read_bytes()
                for directory in (self.source, self.compiled)
                for path in directory.rglob("*")
                if path.is_file()
            },
        )
        barrier = Barrier(2, timeout=10)

        def parallel_run(command):
            barrier.wait()
            return run(command)

        with patch("theorem_graph_sdk.isolated.CommandRunner") as runner:
            runner.return_value.run.side_effect = parallel_run
            parallel = extract_available(
                self.project,
                compiled_root=self.compiled,
                module_prefix="Demo",
                search_paths=[],
                lean_bin=lean_bin,
                output=self.root / "parallel",
                branch="v4.30.0",
                commit="commit",
                repository="repo",
                jobs=2,
                batch_size=1,
                memory_budget_mb=8192,
            )
        self.assertEqual(parallel["completedModules"], ["Demo.A", "Demo.B"])
        self.assertEqual(
            len({attempt["directory"] for attempt in parallel["attempts"]}), 2
        )
        self.assertTrue(
            all(attempt["elapsedSeconds"] >= 0 for attempt in parallel["attempts"])
        )

    @unittest.skipUnless(
        os.environ.get("THEOREM_GRAPH_TEST_LEAN_BIN"), "optional tiny real-Lean smoke"
    )
    def test_real_lean_imports_existing_modules_and_splits_collision(self):
        lean = Path(os.environ["THEOREM_GRAPH_TEST_LEAN_BIN"]).resolve()
        for name, number in (("A", 1), ("B", 2)):
            source = self.source / f"{name}.lean"
            source.write_text(
                f"def helper : Nat := {number}\n/-- Lemma {number}.1: test result. -/\ntheorem result{name} : helper = {number} := rfl\n"
            )
            subprocess.run(
                [
                    str(lean),
                    "-j",
                    "1",
                    "-o",
                    str(self.compiled / "Demo" / f"{name}.olean"),
                    str(source),
                ],
                cwd=self.source,
                check=True,
                capture_output=True,
                text=True,
                timeout=120,
            )
        try:
            report = extract_available(
                replace(self.project, root_module="Demo.A"),
                compiled_root=self.compiled,
                module_prefix="Demo",
                search_paths=[],
                lean_bin=lean,
                output=self.root / "smoke",
                branch="v4.30.0",
                commit="tiny-smoke",
                repository="repo",
                timeout=180,
                memory_mb=2048,
            )
        except ExtractionError as exc:
            self.fail(
                str(exc)
                + "\n"
                + "\n".join(
                    path.read_text()
                    for path in (self.root / "smoke").glob("*/extract.log")
                )
            )
        self.assertEqual(report["completedModules"], ["Demo.A", "Demo.B"])
        self.assertEqual(len(report["attempts"]), 3)
        self.assertEqual(report["failedModules"], [])


if __name__ == "__main__":
    unittest.main()
