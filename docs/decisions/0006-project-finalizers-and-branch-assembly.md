# ADR-0006: Finalize projects independently before branch assembly

## Status

Accepted

## Date

2026-09-05

## Context

A release can contain many books and papers on the same Lean branch.  The
original remote finalizer owns an entire branch: it holds one branch lock,
builds every project's documentation and Verso pages in one Pod, generates all
theorem maps, and publishes one branch site.  Internal Lake concurrency uses a
multi-core Pod efficiently, but adding books increases the critical path and a
single slow project delays every other project on that branch.

Running the existing branch finalizer once per project is unsafe.  Those jobs
would write the same private Lake workspace, Web output directory, logs,
branch site, and `result.json`.  Last-writer-wins overlays would also hide
conflicting routes and would provide no immutable evidence for the individual
projects.

The current branch finalizer is already in use for immutable releases.  New
parallel execution must therefore be opt-in and must not change, stop, or
reinterpret an in-flight branch job.

## Decision

- Keep the branch finalizer as the default and retain its existing result
  contract.  Existing manifests and releases remain valid.
- Add an opt-in project-finalizer manifest containing one independently
  schedulable job per `ProjectSpec`.  A job is bound to the release ID,
  ReleaseSpec digest, tooling digest, branch commit, Lake manifest, toolchain,
  complete project key, and execution configuration.
- Each project worker writes only below its release-scoped project directory:
  `project-finalizers/<branch>/<safe-project-key>/`.  Its site fragment and
  result are published atomically; the result is written last and records the
  content-tree SHA-256, file count, and byte count.
- Project Verso generation requires exactly one canonical project selector.
  It emits an identity-bound route/module inventory, does not rewrite
  branch-wide source overviews or README files, and does not claim the shared
  root catalog.
- A project fragment's disjoint Verso output is part of the executable
  contract, not merely a post-build assertion.  The generic Verso SDK passes
  the normalized absolute directory to `lake exe <site> --output <directory>`
  and rejects non-executable targets or a second explicit `--output`.  This
  keeps the generated files and the fragment manifest under the same worker-
  owned root instead of silently accepting Verso's shared `_site` default.
- A project worker gets a private mutable finalizer workspace.  The immutable
  branch Lean cache remains read-only.  No two project workers share a mutable
  Lake/Web directory or branch result path.
- The build SDK recognizes writable branch/project finalizer workspaces only
  through their exact cache paths and schema-2/schema-3 markers.  Those
  identities bind tooling, branch, optional build configuration, and optional
  project key.  Documentation checkpoints continue to hash their dependency
  artifacts; only a branch cache outside the `finalizer-caches` namespace may
  replace those hashes with immutable namespace metadata.
- Add one branch-assembly job per branch.  It requires the exact project set
  declared by the ReleaseSpec, revalidates every identity and content digest,
  and rejects missing, extra, duplicate, stale, symlinked, or special-file
  artifacts.
- Branch assembly overlays through a collision-checking merger.  Identical
  shared files may be deduplicated; differing bytes, modes, or file/directory
  shapes fail closed.  Project-owned docs, page, and theorem-map roots must
  have exactly one owner.  Only the assembler may create shared branch catalog
  and routing output.
- Branch site publication is staged and atomically replaced.  Only after the
  complete site validates does the assembler write the existing
  `BranchBuildResult`.  The release aggregate continues to consume only those
  branch results and never consumes project partials directly.
- Project jobs and branch assembly are separate scheduling barriers.  Project
  jobs within and across branches may run concurrently; each branch assembler
  starts only after all required project results for that branch succeed.
- Increasing CPU width or changing project/branch execution mode creates a new
  immutable execution identity.  Checkpoints from another configuration are
  not relabelled as compatible.

### Repository boundary

This ADR describes the combined release system, including its operator-local
SiFlow adapter.  The checked-in `sdk/deploy` package owns the portable
`ReleaseSpec`, project/branch result schemas, release layout, aggregate
contract, packaging, validation, and promotion paths.  Provider-specific Pod
manifests, quota admission, credentials, submission/polling, project execution,
and branch-assembly commands live in the repository-local `SiFlow-sdk/`
operator skill.  That directory is intentionally gitignored and is not part of
a public GitHub clone.

Consequently, a clone can verify, preview, publish, and self-host an already
assembled release, but it cannot schedule the SiFlow build phases by itself.
The GitHub Pages workflow consumes only the portable release artifacts and does
not depend on the ignored adapter.  If project finalization is later offered as
a provider-neutral public API, its execution and strict fragment merge engine
must first move into `sdk/deploy`; only the SiFlow resource mapping should
remain in the operator skill.

## Alternatives considered

### Increase a single branch Pod beyond 16 CPUs

This can help until Lake scheduling or shared-storage throughput becomes the
bottleneck, but it does not isolate failures and does not remove the
branch-length critical path.  It remains a supported tuning option, not the
scaling architecture.

### Run the old branch finalizer once for each book

Rejected because all workers would claim shared mutable paths and publish the
same branch result.  Serializing those writes would also eliminate the desired
parallelism.

### Let the release aggregate merge project fragments directly

Rejected because it would mix project completion, branch completeness, and
release packaging into one boundary.  Keeping an explicit branch result
preserves backward compatibility and lets the existing aggregate remain a
strict consumer of complete branches.

### Silently overwrite colliding files in project order

Rejected because output would depend on scheduling/order and a project could
replace another project's route.  Only byte-identical shared files are safe to
deduplicate.

## Consequences

- A branch with many projects can use one remote Pod per project and reduce
  wall-clock time, subject to SiFlow quota and shared-storage throughput.
- Project finalization consumes more temporary storage than a single branch
  workspace.  Operators must size concurrency to available cache space; a
  future sparse/overlay cache may reduce this cost without weakening isolation.
- A project failure can be retried without discarding successful sibling
  artifacts, while branch publication remains all-or-nothing.
- Two remote phases are visible operationally: parallel project finalizers,
  then branch assemblers.  The operator-local one-click deployment command
  orchestrates both barriers.
- The branch finalizer remains useful for small releases and as a compatibility
  path.  Both modes converge on the same validated `BranchBuildResult` contract.
