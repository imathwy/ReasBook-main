# ADR-0007: Keep reader links within the published documentation closure

## Status

Accepted

## Date

2026-09-05

## Context

ReasBook publishes two related but intentionally different views of a Lean
project.  Verso discovers readable source modules from the project tree, while
the API documentation SDK renders only modules reachable from the registered
`Book` or `Paper` Lake root.  A source file can therefore have a valid Verso
page without belonging to the public API import closure.

Historical Verso artifacts generated a `Documentation` link for every
discovered source module.  Two immutable branch artifacts exposed the mismatch:
the reader page existed, but the derived API URL did not.  The release-wide
link-closure check correctly rejected those links.  Adding imports during
deployment would change the Lean library represented by the pinned source
commit, and creating an HTML stub would misrepresent an unexported module as
API documentation.

## Decision

- The `Book`/`Paper` import closure remains the authority for which API pages
  exist.  Deployment never changes that closure and never manufactures an API
  page from Verso content.
- Final site assembly reconciles only the generated pair
  `Documentation` + `Verso`.  If the internal Documentation target is absent
  and the adjacent internal Verso target is a real file, the link is replaced
  by a non-link `Documentation unavailable` status.  The valid Verso link is
  retained.
- Missing links that do not match that exact condition remain unchanged and
  are rejected by the existing strict link-closure verifier.  In particular,
  a missing project root, missing Verso fallback, external URL, or path escape
  cannot be hidden by reconciliation.
- Assembly writes `unavailable-documentation.json`, grouping every downgraded
  Documentation route with its Verso route and referring pages.  This file is
  deterministic release evidence and is included in the final site digest.
- Reconciliation is an assembly behavior, so importing an older immutable
  branch artifact requires a new immutable tooling snapshot and ReleaseSpec.
  Existing branch artifacts and their producer provenance are not modified.
- If an unavailable module should become part of the public API, its source
  project must explicitly import it from the appropriate `Book` or `Paper`
  root in a later source commit.  Rebuilding docs will then make the original
  Documentation link valid without a deployment exception.

## Alternatives considered

### Add missing imports while packaging the release

Rejected because packaging must not mutate the semantics or source identity of
the Lean library.  It would also make the published docs disagree with the
pinned commit in the ReleaseSpec.

### Generate redirect or placeholder API pages

Rejected because a redirect to Verso is not API documentation, and a generic
stub would falsely imply that doc-gen analyzed the module.

### Ignore selected broken links in the verifier

Rejected because the deployed HTML would still contain broken navigation and
the exception list could conceal unrelated regressions.  The visible page is
corrected before a full, exception-free closure check.

### Require Verso and API documentation to discover identical module sets

Rejected because the wider reader view is useful for work-in-progress source
files, while the API view must continue to describe the exported Lean library.

## Consequences

- GitHub Pages and self-hosted deployments retain strict internal link closure
  without presenting a misleading API link.
- Users can still read an unexported module through its valid Verso page and
  can see explicitly why no Documentation navigation is available.
- Release reviewers can audit every downgrade from one small manifest instead
  of searching rendered HTML.
- A growth in the audit manifest is visible evidence that source import roots
  or generator selection deserve follow-up; it is not silently treated as an
  API documentation success.
