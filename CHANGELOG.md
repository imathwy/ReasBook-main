# Changelog

Significant user-facing and release-engineering changes are recorded here.

## Unreleased

### Added

- Reusable build, Verso, theorem-graph, comparator, and deployment SDKs.
- Multi-version `ReleaseSpec` with explicit canonical project selection.
- SiFlow branch finalizers and aggregate packaging backed by a fixed external
  cache.
- Immutable GitHub Release to GitHub Pages publication workflow.

### Changed

- GitHub Pages is a publish-only target; full Lean builds run on SiFlow.
- Repository scripts are thin project adapters while reusable behavior lives
  in the SDK packages.

### Removed

- Superseded top-level wrappers and duplicate theorem-map implementations.
