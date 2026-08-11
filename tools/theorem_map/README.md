# ReasBook theorem maps

This directory contains the branch-independent generator and static frontend for
ReasBook theorem dependency maps. A map shows the natural-language statement of
each literature-level declaration, the matching Lean declaration, and direct
dependencies after project-internal helper declarations are contracted.

The deployment currently publishes only audited, project-provided maps. This
keeps the public site focused while the remaining books and papers are being
reviewed. Projects without a `theorem-map/index.html` are skipped by default.

## Generation

`Extract.lean` reads compiled Lean environments. `generate_all.py` discovers all
book and paper entry points on one version branch and copies audited static maps
under:

```text
ReasBookWeb/_site/theorem-maps/books/<project-id>/
ReasBookWeb/_site/theorem-maps/papers/<project-id>/
```

The Pages workflow checks this generator out from `main` while building every
registered version branch. After those branch artifacts are merged,
`catalog.py` rebuilds the cross-version map index.

Run one branch locally after its Lean root modules have been compiled:

```bash
python3 tools/theorem_map/generate_all.py \
  --repo-root . \
  --site-root ReasBookWeb/_site \
  --branch v4.32.2
```

To preview automatically generated maps for the remaining projects, opt in
explicitly with `--include-generic`. That mode identifies docstrings beginning
with labels such as `Theorem 2.3` and extracts their Lean dependencies.

## Project overrides

A project can provide either of these overrides:

- `theorem-map.json`: curated data rendered by the generic frontend.
- `theorem-map/index.html`: a complete static map copied verbatim. Include a
  `metadata.json` with `project`, `nodes`, and `edges` fields so the shared
  catalog can report accurate counts.

The static override is appropriate when an article has multiple Lean
declarations for one numbered result or its prose requires an audited rendering.
