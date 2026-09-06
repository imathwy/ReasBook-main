# Changelog

Significant user-facing and release-engineering changes are recorded here.

## Unreleased

### Added

- Integrated ReasBook Reviewer with public book/paper reading, authenticated
  comments, persistent review history and cache-reusing container deployment.
- Statement/proof dependency views with bounded depth, natural layout and
  source/docs/Verso navigation in the reader.
- Explicit, source-bound selection of approved single-book Verso producers
  without replacing existing Source, Docs or Graph evidence.
- Reusable build, Verso, theorem-graph, comparator, and deployment SDKs.
- Multi-version `ReleaseSpec` with explicit canonical project selection.
- SiFlow branch finalizers and aggregate packaging backed by a fixed external
  cache.
- Project-scoped Verso fragments and two-barrier branch assembly for running
  independent books and papers concurrently.
- Compact, source-derived Verso readers for books and papers organized as
  declaration-per-file item modules, plus generated indexes for imports-only
  paper sections whose content lives in part modules.
- A release acceptance gate that rejects required Verso outputs which contain
  only an empty generated shell.
- Immutable GitHub Release to GitHub Pages publication workflow.

### Changed

- GitHub Pages is a publish-only target; full Lean builds run on SiFlow.
- GitHub Pages now retains every selected project's API pages while using
  lightweight placeholders only for external dependencies. Its operational
  site budget is 920 MB with an independent 1 GB hard gate; the full historical
  site remains unchanged for self-hosting.
- Book titles may come from a safe top-level `book.yml`/`book.yaml` scalar, and
  generated book, paper-item, and paper-section routes are included in fragment
  ownership manifests without turning every item into a Verso compilation
  target or expanding the sidebar with thousands of item names.
- Repository scripts are thin project adapters while reusable behavior lives
  in the SDK packages.

### Removed

- Superseded top-level wrappers and duplicate theorem-map implementations.
