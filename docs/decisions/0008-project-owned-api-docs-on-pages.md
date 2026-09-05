# ADR-0008: Retain project-owned API documentation on GitHub Pages

## Status

Accepted

## Date

2026-09-05

## Context

ADR-0002 introduced a bounded GitHub Pages projection because the complete
release site is already larger than GitHub Pages' 1 GB published-site limit.
That projection retained only one API entry page per canonical project and
replaced every deeper API link with a small placeholder.

The resulting site fit comfortably within its 850,000,000-byte operational
budget, but it did not provide usable API documentation.  In release
`site-20260905T124421Z-e986b071fe51`, 5,520 of 7,183 HTML files in the Pages
artifact were projection placeholders.  A reader could open a `Book`, `Paper`,
or `Main` entry and then immediately leave the real documentation when
following a chapter or declaration link.

The same release provides enough evidence to choose a more useful boundary:

- the existing Pages artifact is 712,116,853 bytes;
- restoring every ReleaseSpec-owned project API page projects to about
  885 MB; and
- the complete self-hosted artifact is about 2.36 GB and therefore remains
  unsuitable for GitHub Pages.

GitHub documents a [1 GB limit for a published Pages
site](https://docs.github.com/en/pages/getting-started-with-github-pages/github-pages-limits).
The temporary GitHub deployment needs a smaller fail-closed operational
budget, while the long-term self-hosted artifact must remain unchanged.

## Decision

- A `ProjectSpec` is the authority for API-document ownership.  For every
  selected project version on a branch, the Pages projector copies all
  existing documentation shapes derived from its kind and project identifier,
  including nested `Books` or `Papers` layouts, flat namespace directories,
  and a same-name top-level HTML entry.
- Canonical selection continues to control catalog redirects and Verso routes.
  It does not turn a non-canonical project version's API pages into external
  dependency placeholders when a canonical project links to them.
- A project API page may still link to a non-canonical Verso route omitted by
  the Pages history policy. The projector closes that link with a lightweight
  redirect to the project's verified canonical Verso route, preserving the
  matching deep suffix when it exists. This is a history redirect, not an API
  documentation placeholder.
- The projector copies project documentation before computing link closure.
  Consequently, links introduced by detailed project pages participate in the
  same validation pass.
- API pages outside all ReleaseSpec-derived ownership roots become explicit
  external-dependency placeholders only when the verified source already marks
  them external or their namespace is an allowed dependency such as Mathlib,
  Lean, Batteries, or Init. Unknown unmarked namespaces fail closed instead of
  silently hiding a project page.
- The Pages operational limit is 920,000,000 bytes.  A separate
  1,000,000,000-byte GitHub hard limit is enforced independently in profile
  validation, local projection, bundle verification, and the publish workflow.
  Raising the operational budget cannot disable the host limit.
- Capacity overflow fails during local or remote packaging before an immutable
  Release is published.  Selection is never changed implicitly to make an
  oversized artifact fit.
- The `full` artifact, its version-qualified URLs, and the self-hosted atomic
  installation process are unchanged.

This decision supersedes ADR-0002 only where it says that Pages retains project
entry API pages while replacing detailed project API pages with placeholders.
ADR-0002 continues to govern target-specific bundles, canonical history,
ReleaseSet binding, immutable publication, and self-hosted delivery.

## Alternatives considered

### Keep only project API entry pages

Rejected because the entry is not useful when its first project-module link
leads to a generic capacity notice.

### Copy every versioned documentation directory without ownership checks

Rejected because it erases the contract between project content and external
dependencies.  ReleaseSpec-derived roots make the boundary deterministic and
cause an unknown project layout to fail instead of being silently reclassified.

### Set the operational budget equal to GitHub's hard limit

Rejected because metadata and normal project growth need headroom.  The
920 MB budget leaves an independent 80 MB host margin and makes the next
capacity decision explicit.

### Change or trim the self-hosted artifact

Rejected because the full artifact is the durable deployment target and is not
subject to GitHub Pages' temporary hosting constraint.

## Consequences

- Detailed project API links work on GitHub Pages and remain byte-identical to
  the verified branch output.
- External dependency links remain visibly bounded instead of silently
  increasing the artifact with transitive documentation.
- Links from retained historical API pages to omitted historical Verso pages
  converge on the explicit canonical project version without copying the
  approximately 152 MB historical route trees.
- The current release family has roughly 35 MB of operational headroom.  A
  future release that crosses 920 MB must reduce a measured large component
  (for example a generated Verso route) or move public serving to the
  self-hosted deployment; it must not restore broad placeholders implicitly.
- Changing this projection and its capacity policy changes the artifact-policy
  digest and therefore requires a new immutable Release.  Existing Lean,
  documentation, Verso, and theorem-map branch artifacts remain reusable after
  identity revalidation.
