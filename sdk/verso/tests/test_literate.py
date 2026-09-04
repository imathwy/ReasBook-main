from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from reasbook_sdk_common import CommandResult
import verso_build_sdk.literate as literate_module
from verso_build_sdk.literate import (
    LiterateCacheBuilder,
    LiterateCacheError,
    LiterateCacheIdentity,
    UnsafeLiterateCacheError,
    load_module_manifest,
)


def modules_digest(modules: list[str]) -> str:
    value = json.dumps(modules, ensure_ascii=True, separators=(",", ":"))
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


class ArtifactRunner:
    def __init__(self, cache: Path, *, fail_call: int | None = None) -> None:
        self.cache = cache
        self.fail_call = fail_call
        self.calls = []

    def run(self, command):
        self.calls.append(command)
        if self.fail_call == len(self.calls):
            return CommandResult(command=command, returncode=7)
        self.assert_command(command)
        for target in command.argv[2:]:
            module = target.removeprefix("+").removesuffix(":literate")
            output = (
                self.cache
                / "build"
                / "literate"
                / Path(*module.split(".")).with_suffix(".json")
            )
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps([{"module": module}]), encoding="utf-8")
            Path(f"{output}.hash").write_text("0123456789abcdef", encoding="ascii")
            Path(f"{output}.trace").write_text(
                json.dumps({"schemaVersion": "test", "module": module}),
                encoding="utf-8",
            )
        return CommandResult(command=command, returncode=0)

    @staticmethod
    def assert_command(command) -> None:
        if command.argv[1] != "build":
            raise AssertionError(command.argv)
        if command.env_dict.get("LAKE_JOBS") != "2":
            raise AssertionError(command.env_dict)
        if command.env_dict.get("LEAN_NUM_THREADS") != "2":
            raise AssertionError(command.env_dict)
        if "LAKE" in command.env_dict:
            raise AssertionError("inherited Lake environment was not scrubbed")


class LiterateCacheTests(unittest.TestCase):
    def fixture(self, root: Path, modules: list[str] | None = None):
        modules = modules or ["Books.Demo.Book", "Books.Demo.Chap01"]
        lean = root / "ReasBook"
        cache = root / "cache"
        web = root / "ReasBookWeb"
        lean.mkdir()
        cache.mkdir()
        web.mkdir()
        (lean / ".lake").symlink_to(cache, target_is_directory=True)
        (lean / "lakefile.lean").write_text(
            "import Lake\npackage Demo where\n", encoding="utf-8"
        )
        (lean / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
        (lean / "lean-toolchain").write_text(
            "leanprover/lean4:v4.30.0\n", encoding="utf-8"
        )
        manifest = web / ".literate-modules.json"
        manifest.write_text(
            json.dumps({"schema_version": 1, "modules": modules}),
            encoding="utf-8",
        )
        identity = LiterateCacheIdentity(
            branch="v4.30.0",
            commit="a" * 40,
            lake_manifest_sha256="b" * 64,
            toolchain="leanprover/lean4:v4.30.0",
            architecture="x86_64",
            modules_sha256=modules_digest(modules),
            source_tree_sha256=literate_module._source_tree_digest(lean),
            tooling_sha256="c" * 64,
        )
        return lean, cache, manifest, identity

    def builder(
        self,
        lean,
        manifest,
        identity,
        runner,
        *,
        chunk_size=1,
        adopt_existing=False,
    ):
        return LiterateCacheBuilder(
            lean_root=lean,
            module_manifest=manifest,
            identity=identity,
            lake_bin="/test/lake",
            jobs=2,
            chunk_size=chunk_size,
            adopt_existing=adopt_existing,
            runner=runner,
            environ={"PATH": "/bin", "LAKE": "stale"},
        )

    def test_populates_batches_then_reuses_verified_marker(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            modules = [f"Books.Demo.Section{i:02d}" for i in range(5)]
            lean, cache, manifest, identity = self.fixture(Path(temp), modules)
            runner = ArtifactRunner(cache)

            first = self.builder(lean, manifest, identity, runner, chunk_size=2).run()
            self.assertFalse(first.reused)
            self.assertEqual(first.scheduled_count, 5)
            self.assertEqual(first.batch_count, 3)
            self.assertEqual([len(call.argv) - 2 for call in runner.calls], [2, 2, 1])
            marker = json.loads(first.marker.read_text(encoding="utf-8"))
            self.assertEqual(marker["identity"], identity.public_dict())
            self.assertEqual(len(marker["artifacts"]), 5)

            reused = self.builder(lean, manifest, identity, runner, chunk_size=2).run()
            self.assertTrue(reused.reused)
            self.assertEqual(reused.scheduled_count, 0)
            self.assertEqual(len(runner.calls), 3)

    def test_corrupt_artifact_removes_marker_and_is_rebuilt(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            lean, cache, manifest, identity = self.fixture(Path(temp))
            runner = ArtifactRunner(cache)
            result = self.builder(lean, manifest, identity, runner).run()
            output = cache / "build/literate/Books/Demo/Book.json"
            output.write_text("[", encoding="utf-8")

            rebuilt = self.builder(lean, manifest, identity, runner).run()
            self.assertFalse(rebuilt.reused)
            self.assertEqual(
                json.loads(output.read_text(encoding="utf-8"))[0]["module"],
                "Books.Demo.Book",
            )
            self.assertTrue(result.marker.is_file())

    def test_failed_batch_never_commits_completion_marker(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            modules = [f"Books.Demo.Section{i:02d}" for i in range(3)]
            lean, cache, manifest, identity = self.fixture(Path(temp), modules)
            failing = ArtifactRunner(cache, fail_call=2)

            with self.assertRaisesRegex(LiterateCacheError, "exited 7"):
                self.builder(lean, manifest, identity, failing).run()
            marker = cache / "build/literate/.reasbook-complete.json"
            self.assertFalse(marker.exists())

            retry = ArtifactRunner(cache)
            completed = self.builder(lean, manifest, identity, retry).run()
            self.assertFalse(completed.reused)
            self.assertEqual(completed.scheduled_count, 2)
            retry_targets = [
                target
                for call in retry.calls
                for target in call.argv[2:]
            ]
            self.assertNotIn("+Books.Demo.Section00:literate", retry_targets)
            self.assertTrue(marker.is_file())

    def test_exact_cache_can_adopt_valid_unmarked_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            lean, cache, manifest, identity = self.fixture(Path(temp))
            initial = ArtifactRunner(cache)
            self.builder(lean, manifest, identity, initial).run()
            (cache / "build/literate/.reasbook-complete.json").unlink()
            (cache / "build/literate/.reasbook-progress.json").unlink()
            adopting = ArtifactRunner(cache)

            result = self.builder(
                lean,
                manifest,
                identity,
                adopting,
                adopt_existing=True,
            ).run()

            self.assertTrue(result.reused)
            self.assertEqual(result.scheduled_count, 0)
            self.assertEqual(adopting.calls, [])

    def test_identity_change_forces_lake_revalidation(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            lean, cache, manifest, identity = self.fixture(Path(temp))
            runner = ArtifactRunner(cache)
            self.builder(lean, manifest, identity, runner).run()
            changed = LiterateCacheIdentity(
                **{**identity.public_dict(), "commit": "c" * 40}
            )

            result = self.builder(
                lean, manifest, changed, runner, adopt_existing=True
            ).run()
            self.assertFalse(result.reused)
            self.assertEqual(len(runner.calls), 4)

    def test_source_change_during_batch_never_advances_state(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            lean, cache, manifest, identity = self.fixture(Path(temp))

            class MutatingRunner(ArtifactRunner):
                def run(self, command):
                    result = super().run(command)
                    (lean / "Changed.lean").write_text(
                        "import Mathlib\n", encoding="utf-8"
                    )
                    return result

            with self.assertRaisesRegex(LiterateCacheError, "source tree changed"):
                self.builder(
                    lean, manifest, identity, MutatingRunner(cache)
                ).run()
            self.assertFalse(
                (cache / "build/literate/.reasbook-progress.json").exists()
            )
            self.assertFalse(
                (cache / "build/literate/.reasbook-complete.json").exists()
            )

    def test_source_change_during_marker_verification_prevents_reuse(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            lean, cache, manifest, identity = self.fixture(Path(temp))
            runner = ArtifactRunner(cache)
            self.builder(lean, manifest, identity, runner).run()
            checking = self.builder(lean, manifest, identity, runner)
            validate = checking._validate_recorded_artifacts

            def validate_then_mutate(modules, records):
                artifacts = validate(modules, records)
                (lean / "Changed.lean").write_text(
                    "import Mathlib\n", encoding="utf-8"
                )
                return artifacts

            with patch.object(
                checking,
                "_validate_recorded_artifacts",
                side_effect=validate_then_mutate,
            ), self.assertRaisesRegex(LiterateCacheError, "source tree changed"):
                checking.run()
            self.assertEqual(len(runner.calls), 2)

    def test_symlink_artifact_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            lean, cache, manifest, identity = self.fixture(root)
            output = cache / "build/literate/Books/Demo/Book.json"
            output.parent.mkdir(parents=True)
            sentinel = root / "sentinel.json"
            sentinel.write_text("[]", encoding="utf-8")
            output.symlink_to(sentinel)

            with self.assertRaises(UnsafeLiterateCacheError):
                self.builder(lean, manifest, identity, ArtifactRunner(cache)).run()
            self.assertEqual(sentinel.read_text(encoding="utf-8"), "[]")

    def test_symlinked_state_and_lock_files_fail_closed(self) -> None:
        for name in (
            ".reasbook-complete.json",
            ".reasbook-progress.json",
            ".reasbook.lock",
        ):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                lean, cache, manifest, identity = self.fixture(root)
                literate = cache / "build/literate"
                literate.mkdir(parents=True)
                sentinel = root / "sentinel"
                sentinel.write_text("unchanged", encoding="utf-8")
                (literate / name).symlink_to(sentinel)

                with self.assertRaises(UnsafeLiterateCacheError):
                    self.builder(
                        lean, manifest, identity, ArtifactRunner(cache)
                    ).run()
                self.assertEqual(
                    sentinel.read_text(encoding="utf-8"), "unchanged"
                )

    def test_manifest_rejects_duplicates_unsafe_names_and_symlinks(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            manifest = root / "modules.json"
            for modules in (
                ["Books.Demo.Book", "Books.Demo.Book"],
                ["../escape"],
                ["-option"],
            ):
                manifest.write_text(
                    json.dumps({"schema_version": 1, "modules": modules}),
                    encoding="utf-8",
                )
                with self.assertRaises(LiterateCacheError):
                    load_module_manifest(manifest)
            target = root / "target.json"
            target.write_text(
                json.dumps({"schema_version": 1, "modules": ["Demo"]}),
                encoding="utf-8",
            )
            manifest.unlink()
            manifest.symlink_to(target)
            with self.assertRaises(UnsafeLiterateCacheError):
                load_module_manifest(manifest)

    def test_cli_identity_checks_claimed_checkout_inputs_and_hashes_sources(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            lean, _, manifest, _ = self.fixture(Path(temp))
            modules = list(load_module_manifest(manifest))
            actual_manifest = hashlib.sha256(
                (lean / "lake-manifest.json").read_bytes()
            ).hexdigest()
            environment = {
                "REASBOOK_GITHUB_BRANCH": "v4.30.0",
                "REASBOOK_SOURCE_COMMIT": "a" * 40,
                "REASBOOK_LAKE_MANIFEST_SHA256": actual_manifest,
                "VERSO_TOOLCHAIN": "leanprover/lean4:v4.30.0",
                "REASBOOK_TOOLING_SHA256": "c" * 64,
            }
            with patch.object(
                literate_module, "_git_value", return_value="a" * 40
            ):
                first = literate_module._default_identity(
                    lean, modules, environment
                )
                (lean / "Books.lean").write_text(
                    "import Mathlib\n", encoding="utf-8"
                )
                second = literate_module._default_identity(
                    lean, modules, environment
                )
            self.assertNotEqual(first.source_tree_sha256, second.source_tree_sha256)

            invalid_values = {
                "REASBOOK_SOURCE_COMMIT": "b" * 40,
                "REASBOOK_LAKE_MANIFEST_SHA256": "d" * 64,
                "VERSO_TOOLCHAIN": "leanprover/lean4:v4.26.0",
            }
            for name, value in invalid_values.items():
                with self.subTest(name=name), patch.object(
                    literate_module, "_git_value", return_value="a" * 40
                ), self.assertRaises(LiterateCacheError):
                    literate_module._default_identity(
                        lean, modules, {**environment, name: value}
                    )

    def test_large_json_validation_is_streaming(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "large.json"
            output.write_bytes(
                b"[" + b" " * (literate_module._JSON_DOM_LIMIT + 1) + b"]"
            )
            metadata = output.stat()
            with patch.object(
                literate_module.json,
                "loads",
                side_effect=AssertionError("large JSON must not build a DOM"),
            ):
                digest = LiterateCacheBuilder._inspect_literate_json(
                    output, metadata
                )
            self.assertEqual(digest, hashlib.sha256(output.read_bytes()).hexdigest())

            output.write_bytes(
                b"[" + b"x" * (literate_module._JSON_DOM_LIMIT + 1) + b"]"
            )
            with self.assertRaisesRegex(LiterateCacheError, "invalid literate JSON"):
                LiterateCacheBuilder._inspect_literate_json(
                    output, output.stat()
                )


if __name__ == "__main__":
    unittest.main()
