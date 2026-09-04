# ADR-0004: Prebuild literate JSON behind an identity-bound cache gate

## Status

Accepted

## Date

2026-09-04

## Context

Verso pages load one SubVerso `+Module:literate` JSON artifact for every
published Lean module. The version branches deliberately support
`REASBOOK_LITERATE_PREBUILT=1`, but the release finalizer previously entered
the site build without first satisfying that contract. On v4.26 this made one
finalizer execute 746 targets serially; several individual modules took many
minutes, so a healthy build could exceed the six-hour stage limit.

The JSON lives in the exact branch Lake cache and is useful across releases,
but file existence alone is not a safe completion signal. An interrupted Lake
process can leave a zero-length or truncated JSON file, and Lake trace files
contain checkout-specific paths. A release must not enable prebuilt mode for a
partial or differently identified cache.

## Decision

- `gen_sections.py` atomically emits `.literate-modules.json`, a deterministic
  schema-1 ordered list of selected Lean modules. Cache tooling consumes this
  manifest instead of parsing human-oriented generated Lean source.
- The Verso SDK owns a separate `verso-literate` capability. It runs before
  the generic site builder and executes bounded batches of
  `+Module:literate` targets. Each batch is one Lake process with a controlled
  `LEAN_NUM_THREADS` value (and `LAKE_JOBS` for forward compatibility);
  batches remain sequential. The capability also takes a cache-local file
  lock. The outer release finalizer continues to own its broader exclusive
  exact-branch-cache lock, so local or remote processes cannot race to mutate
  the literate cache.
- The completion marker binds branch, full source commit, Lake-manifest
  SHA-256, Lean toolchain, architecture, ordered-module digest, actual Lean
  source-tree digest, tooling SHA-256, and an explicit cache profile. Supplied
  commit, manifest, and toolchain claims must match the checkout. Every
  expected JSON must be a
  non-symlink regular non-empty UTF-8 JSON array. Its Lake hash must be exactly
  16 lowercase hexadecimal bytes, its trace must be a JSON object, and the
  marker records JSON size/SHA-256, Lake hash, and trace SHA-256.
- The source-tree and module-manifest digests are recomputed before each
  successful batch checkpoint and before final completion. An observed edit
  during a long extraction fails the run without blessing mixed artifacts.
- A same-directory atomic progress checkpoint binds each successfully
  validated batch to that exact identity. A retry verifies the checkpointed
  hashes and schedules only missing or corrupt modules; it does not depend on
  checkout-specific Lake trace paths for cross-run reuse. The final marker is
  written by same-directory atomic replacement only after every
  artifact validates. A marker and all recorded artifacts must validate again
  before a later run skips Lake entirely. An invalid generated artifact is
  removed so Lake cannot trust a stale trace; symlinks and special files fail
  closed and are never followed or replaced.
- A failed batch never advances the progress checkpoint or writes the final
  marker. Previously checkpointed batches remain reusable. A finalizer may
  explicitly adopt valid unmarked artifacts only because it has independently
  derived and locked the exact immutable branch-cache key; ordinary local
  builds cannot opt into that trust implicitly.
- Marker hits verify recorded size and SHA-256 in a single streaming read.
  Newly generated small JSON is parsed fully. Large JSON is UTF-8 decoded and
  checked with a complete iterative mmap-backed grammar parser without
  constructing a multi-gigabyte Python DOM. Mapped file pages can still count
  toward process RSS up to roughly the current artifact size; validation runs
  after the Lake subprocess has exited. The successful Lake command,
  exact Lake hash/trace, and recorded SHA-256 provide additional provenance.
- `scripts/build/verso.sh` runs the generator once, completes this cache gate,
  and only then exports `REASBOOK_LITERATE_PREBUILT=1`. The generic Verso
  generator hook is cleared to avoid a second, potentially divergent
  generation pass.

## Alternatives considered

### Increase the Verso timeout

Rejected because it leaves hundreds of independent targets serialized and
turns ordinary retries into many hours of repeated work.

### Start one Lake process per module in parallel

Rejected because multiple Lake processes would concurrently update the same
cache metadata and duplicate dependency scheduling. One Lake process per
bounded batch preserves Lake's scheduler and process-tree cancellation.

### Trust JSON existence or Lake traces alone

Rejected because an interrupted writer can leave an existing but incomplete
artifact, while trace inputs include an ephemeral finalizer checkout path.

### Store literate JSON in the web cache or release directory

Rejected because extraction is a derivative of the Lean branch source,
manifest, and toolchain. The exact branch cache is the reusable ownership
boundary; web and release caches have different identities and lifetimes.

## Consequences

- Large branches use the CPUs assigned to one SiFlow finalizer while retaining
  a single cache writer and bounded memory/process fan-out.
- The first complete extraction remains expensive, but it is resumable; later
  feature and clean-main release finalizers can verify hashes and skip Lake
  extraction entirely when their identity is unchanged.
- Tooling, module selection, source revision, dependency manifest, toolchain,
  or architecture changes invalidate the marker deterministically.
- Marker verification streams and hashes every expected artifact once. This
  adds about one full-cache read on reuse, without memory proportional to the
  largest JSON tree, in exchange for refusing stale or truncated release
  inputs.
