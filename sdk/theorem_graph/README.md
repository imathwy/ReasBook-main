# Theorem Graph SDK

theorem-graph-sdk turns Lean declaration metadata into a stable,
literature-oriented theorem dependency graph. It owns graph analysis,
extraction, rendering, publication, the Lean extractor, and static frontend
resources. It has no task-scheduler dependency.

The architecture has three replaceable layers:

- analysis: pure parsing, representative selection, and helper-dependency
  contraction;
- extractor: a protocol plus compiled-environment and source fallback
  implementations;
- render/generator: JSON, static assets, catalog generation, and atomic
  publication.

## CLI

From this repository, a generated map can be built with:

    ./sdk/theorem_graph/bin/theorem-graph \
      --repo-root . --site-root ReasBookWeb/_site --branch v4.32.2

Curated projects are copied by default. To generate maps for projects without a
curated theorem-map directory, opt in explicitly:

    ./sdk/theorem_graph/bin/theorem-graph \
      --repo-root . --site-root ReasBookWeb/_site --branch v4.32.2 \
      --include-generic

The packaged resources are used by default; `--extractor` and `--assets`
allow explicit replacements. Compiled extraction failures fall back to source
comments unless `--no-source-fallback` is supplied. The output tree is staged
and atomically replaced, so a failed run leaves the previous published tree
intact. Use `--extractor-timeout-seconds` to bound compiled-environment
extraction.

## Python API

    from pathlib import Path
    from theorem_graph_sdk import GraphGenerator, TheoremGraphConfig

    config = TheoremGraphConfig(
        repo_root=Path("."),
        site_root=Path("ReasBookWeb/_site"),
        branch="v4.32.2",
    )
    report = GraphGenerator(config).generate()

For tests or a different extraction service, pass an object implementing
DeclarationExtractor to GraphGenerator(extractor=...). The extractor only
returns JSON-compatible declaration records; it never edits Lean source files.

Rebuild a catalog after merging branch artifacts with:

    ./sdk/theorem_graph/bin/theorem-graph catalog --site-root .site
