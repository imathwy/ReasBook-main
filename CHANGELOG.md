# Changelog

Significant user-facing and release-engineering changes are recorded here.

## Unreleased

### Added

- Reusable build, Verso, theorem-graph, comparator, and deployment SDKs.
- Multi-version `ReleaseSpec` with explicit canonical project selection.
- SiFlow branch finalizers and aggregate packaging backed by a fixed external
  cache.
- Project-scoped Verso fragments and two-barrier branch assembly for running
  independent books and papers concurrently.
- Immutable GitHub Release to GitHub Pages publication workflow.

### Changed

- GitHub Pages is a publish-only target; full Lean builds run on SiFlow.
- GitHub Pages now retains every selected project's API pages while using
  lightweight placeholders only for external dependencies. Its operational
  site budget is 920 MB with an independent 1 GB hard gate; the full historical
  site remains unchanged for self-hosting.
- Repository scripts are thin project adapters while reusable behavior lives
  in the SDK packages.

### Removed

- Superseded top-level wrappers and duplicate theorem-map implementations.
