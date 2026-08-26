# Contributing to ReasBook

Thank you for contributing! This guide is for book/paper contributors. Each contributor is
responsible for one or more books/papers; by default each book is developed on its own branch
and submitted as a PR.

## 1. Choose the target version branch

From the **Toolchain Branches** table in the main README, pick the stable branch that exactly
matches the Lean/mathlib version of your book project:

```text
v4.26.0
v4.30.0
v4.32.0
v4.32.2
```

ReasBook only accepts stable `vX.Y.Z` versions that are registered in the main
README and `config/toolchains.yml`. Patch releases are allowed when explicitly
registered; release candidates and nightlies are **not** accepted.
The PR target version must match `ReasBook/lean-toolchain`. Do **not** target `main` with book code.

If the version you need is not listed, contact a maintainer. Do not switch to a nearby version
on your own, and do not submit a new-version PR to an old version branch.

## 2. Fork and create a personal branch

Fork [optpku/ReasBook](https://github.com/optpku/ReasBook), then create your branch from the
latest state of the target version branch:

```bash
git fetch upstream
git switch -c book/<book-slug> upstream/vX.Y.Z
```

Use lowercase letters, digits, and hyphens for the branch name, for example:

```text
book/analysis2-tao-2022
```

## 3. Add your book

Put the book under:

```text
ReasBook/Books/<BookId>/
```

The Book ID uses:

```text
<Title>_<AuthorLastName>_<Year>
```

For example:

```text
Analysis2_Tao_2022
```

`sorry`/`admit` are allowed in the source, but they must be reported truthfully in the PR report.

Keep all existing books and papers in the target version branch. Do not delete or overwrite
other content, and do not modify the root README on `main`.

## 4. Add book documentation

Add a `README.md` in the book directory with at least:

- Full book title, author, edition, and year;
- contributor names and GitHub usernames;
- Lean toolchain;
- coverage;
- declarations, lines of code, proof completion, and `sorry`/`admit` counts.

> Build instructions are the same for every book (see §5: `cd ReasBook && lake build`);
> individual book READMEs do not need to repeat the build command.

If the repository provides a `book.yml` template and a validation script, also fill in the
`book.yml` for the book. Use `null` for unknown fields; do not invent values.

## 5. Build and check

Run the full build command specified by the maintainers from the Lean project directory, e.g.:

```bash
cd ReasBook
lake build
```

You may first run `lake exe cache get` to pull prebuilt mathlib artifacts (optional; falls back
to local compilation). Full Lean builds and web builds run on the maintainer's self-hosted
runner; for local verification, `lake build` passing is usually sufficient.

Before committing, check that you did not accidentally delete files from the target branch:

```bash
git diff --diff-filter=D --name-status upstream/vX.Y.Z...HEAD
```

Apart from intentional replacements inside your own book, there should be no deletions of other
books or papers.

## 6. Submit a PR

Set the PR base to the matching version branch:

```text
vX.Y.Z
```

New book PR title:

```text
[Book][vX.Y.Z] Add <BookId>
```

Update PR title:

```text
[Book][vX.Y.Z] Update <BookId>: <short-scope>
```

For example:

```text
[Book][v4.30.0] Add Analysis2_Tao_2022
```

## 7. PR body template

```markdown
## Book contribution report

- **Book:** <Title> — <Author full name> (<Edition, Year>)
- **Book ID:** `<BookId>`
- **Contributor:** <Name> (@<GitHub-ID>)
- **Target branch:** `vX.Y.Z`
- **Lean toolchain:** `<full content of ReasBook/lean-toolchain>`
- **Declarations:** <total> (theorem/lemma/example: <count>; other: <count>)
- **Lean code:** <file-count> `.lean` files, <line-count> lines
- **Proof completion:** <done> / <total> = <percent>%
- **Remaining placeholders:** `sorry`: <count>; `admit`: <count>
- **Book metadata:** book `README.md` added; `book.yml` added / not yet enabled in this repository

### Summary

<2–4 sentences on the covered chapters or main content, and what is not yet done.>
```

## Pre-submission checklist

- Personal branch created from the correct `upstream/vX.Y.Z`.
- PR base, PR title, and `lean-toolchain` version are consistent.
- Branch name, book directory name, and PR title follow the conventions.
- Book `README.md` and contributor info are complete.
- Other books and papers in the target version branch are preserved.
- **Local build passes**: Run `lake build` in the `ReasBook/` directory and verify
  no errors. Attach the build output summary to the PR.
- **PR CI will run automatically**: The `deploy_pages` workflow is triggered on
  pull requests to `v4.30.0` and `v4.32.0`. It runs a quick build of changed files.
  CI must pass before the PR can be merged.

## After PR submission

1. **Watch the CI**: A GitHub Actions workflow will start automatically. If it fails,
   check the logs and fix the issues.
2. **Maintainer review**: A maintainer will review the PR. They may request changes
   or merge it directly if everything is in order.
3. **Merged PRs are deployed**: After merging to `v4.30.0` or `v4.32.0`, the next
   `deploy_pages` run on `main` will include the updated book in the public site.
- Full build passes and the reported statistics are truthful.
- No `.lake/`, caches, logs, or generated websites are committed.
