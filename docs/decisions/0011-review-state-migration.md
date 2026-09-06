# ADR 0011: Preserve legacy review state until an explicit migration

## Status

Accepted

## Context

The integrated reviewer stores records under the compound identity
`(book_slug, item_key, actor_id)`. The former Stacks reviewer database uses
`(tag, actor_id)`, and historical tags are not always one-to-one with theorem
items. Guessing an item from a legacy tag could attach comments to the wrong
theorem.

## Decision

Do not automatically copy, rewrite, or delete the legacy SQLite database.
Treat it as a read-only migration source until a versioned mapping and explicit
operator approval exist. New deployments use the canonical database under the
configured reviewer state directory and keep the legacy file outside the
ReasBook checkout.

A future migration must snapshot and checksum the source, resolve every tag to
an unambiguous `(book_slug, item_key)` (or report it for manual review),
preserve event provenance, be idempotent, and produce a dry-run report before
writing canonical records.

## Consequences

Existing comments remain available in the legacy reviewer until migration is
performed, while the integrated reviewer cannot silently corrupt them.
Operators should back up both databases and plan an explicit cutover; startup
does not migrate state.
