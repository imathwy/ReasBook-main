---
name: reasbook-contributing
description: Prepare or review a ReasBook book or paper source contribution on the correct versioned Lean branch. Use when adding or updating a formalization, checking its layout and metadata, validating it locally, or preparing its pull request. Do not use for main-branch SDK, release, or website changes.
---

# ReasBook Contributing

Help produce a reviewable source contribution without crossing Lean toolchain
boundaries or modifying unrelated projects.

## Establish the contribution contract

Read [`../CONTRIBUTING.md`](../CONTRIBUTING.md) before changing files. Treat it
as the human-facing procedure and this skill as the agent execution contract.

Determine these values from evidence before editing:

- kind: `book` or `paper`;
- exact, case-sensitive project ID;
- exact Lean/mathlib version;
- target `vX.Y.Z` branch and its registry status; and
- whether this is an addition or an update.

Read `config/toolchains.yml` from `main`, then inspect
`ReasBook/lean-toolchain` and `ReasBook/lakefile.lean` on the target branch.
Normally target only an `Active` branch. Stop for maintainer direction if the
version is unregistered or not active; never silently choose a nearby version.

## Work on the version branch

Book and paper source does not belong on `main`. Create a branch from the
current upstream version ref using `book/<slug>-vX.Y.Z` or
`paper/<slug>-vX.Y.Z`.

Use the branch's existing layout rather than assuming all toolchains are the
same:

- books live in `ReasBook/Books/<ProjectId>/` with `Book.lean` as the
  documentation/check root;
- papers live in `ReasBook/Papers/<ProjectId>/` with `Paper.lean` as the root;
- project library registration may be shared, per-project, or explicit-root;
  follow the target `lakefile.lean` pattern; and
- preserve all unrelated source and user changes.

Every project needs an accurate README. Books use `book.yml` where that branch
supports the metadata contract; papers currently do not use `paper.yml`.
Never infer unknown bibliography, coverage, statistics, or placeholder counts.
Use Python 3.11 or newer for repository metadata helpers.

## Validate proportionally

Check the root file directly with the branch-pinned toolchain:

```bash
cd ReasBook
lake exe cache get
lake env lean Books/<ProjectId>/Book.lean
# or: lake env lean Papers/<ProjectId>/Paper.lean
```

The cache command is optional. Use a dedicated `lake build <ProjectId>` only
when the branch defines that library. Do not launch repository-wide or remote
builds unless the user requests them; record any validation not run.

Before handoff, compare against `upstream/vX.Y.Z`, inspect deletions separately,
and ensure generated caches, sites, logs, and compiled artifacts are absent.
Do not claim PR CI ran: workflow coverage varies by version branch.

## Prepare the handoff

Use the kind-specific `[Book]` or `[Paper]` PR title from the contribution
guide. Report the exact base branch, toolchain, changed scope, commands run,
results, placeholder counts, and any validation still pending. Do not commit,
push, or open a PR unless the user asked for that external action.
