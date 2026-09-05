# ADR-0005: Treat Lake and Lean concurrency as separate controls

## Status

Accepted

## Date

2026-09-04

Updated 2026-09-05 to cover the post-Lake validation process pool and the
stage-specific generated-site Lake scheduler.

## Context

A SiFlow task has three distinct resource controls:

- `instance_count_per_pod` allocates vCPUs and proportional memory;
- the Lake executable schedules asynchronous build jobs in its runtime task
  pool; and
- every child `lean` compiler has its own worker pool.

These controls are not interchangeable. In the supported Lean releases,
Lake is a generated Lean executable, so its runtime task manager reads
`LEAN_NUM_THREADS`. The `lean` shell instead takes its worker count from the
explicit `-j` argument. `LAKE_JOBS` is not interpreted by these Lake versions.
The relevant upstream behavior is visible in Lean's
[`lean_init_task_manager`](https://github.com/leanprover/lean4/blob/v4.30.0/src/runtime/object.cpp#L978-L1003)
and generated executable
[`main`](https://github.com/leanprover/lean4/blob/v4.30.0/src/Lean/Compiler/LCNF/EmitC.lean#L1091-L1130).

Applying the same value at both scheduler levels can create up to the product
of the two widths in runnable Lean workers. The Pod cpuset still bounds actual
CPU time, but excess processes and threads can add scheduling and memory
pressure. Conversely, requesting more SiFlow units without widening either a
useful scheduler or CPU affinity does not make a stage faster.

Verso adds a fourth, non-nested phase after Lake exits: generated JSON is
hashed, checked as UTF-8, and parsed with an mmap-backed grammar validator.
Representative 0.85 GiB validation took about 71.5 seconds on one worker,
36.8 seconds on two, and 24.9 seconds on four; eight workers did not improve
the skewed sample because one large artifact set the critical path. This work
is CPU-bound and does not overlap the Lake or child Lean worker pools.

The child `-j` value is also a Lake trace input. The release finalizer injects
it into a detached `lakefile.lean`, which makes it part of the source-tree and
cache identity. Silently changing an existing branch cache from `-j 8` to
`-j 1` would therefore discard valid literate checkpoints or force a broad
core rebuild even though the mathematical sources are unchanged.

The outer Verso deadline covers both resumable literate extraction and the
subsequent generated-site build. On v4.26, measured/estimated full work is
6.4--8.4 hours for literate extraction followed by 8--10 hours for 746 pages;
a 24-hour deadline leaves too little operational margin around both phases.

## Decision

- `instance_count_per_pod` and `cpu_list` describe the hard task allocation.
  Submission must validate both before credential input or remote creation.
- `lake_threads` means Lake runtime task-pool workers and is implemented with
  `LEAN_NUM_THREADS` on the Lake process.
- `lean_threads` means workers inside core/literate child compilers.
  `web_lean_threads` independently means workers inside each generated-site
  child compiler. Both are implemented with an explicit package-level
  `moreLeanArgs := #["-j", "N"]` in their respective detached lakefiles.
  An existing assignment is rewritten only when its unique `-j` value can be
  identified; an ambiguous assignment fails closed.
- `LAKE_JOBS` is not a supported control and must not appear in generated task
  environments or documentation as one.
- The Verso SDK's `--jobs` option controls the outer Lake runtime pool only.
  The standalone SDK cannot claim a total CPU budget because it does not own
  the caller's package-level child `-j` setting.
- Verso exposes a separate `validation_jobs` / `--validation-jobs` control for
  read-only post-batch artifact validation. Its portable SDK default is one,
  its hard limit is eight, and the full release finalizer explicitly selects
  four while smaller canaries are capped by their configured CPU width.
  It uses spawned processes, submits larger artifacts first, reports errors in
  module-manifest order, and advances the checkpoint only after every artifact
  in the batch succeeds. Repairing progress and adopting existing artifacts
  remain serial because those paths can delete invalid files.
- Validation concurrency is an execution strategy, not an artifact input. It
  does not change the source/cache identity or invalidate Lake traces.
- The final generated-site build has an explicit `web_lake_threads` outer Lake
  width, passed only through `VERSO_ENV_LEAN_NUM_THREADS`. Its automatic value
  is capped at 16 and at `floor(available CPUs / web_lean_threads)`; the
  orchestrator rejects a larger nested product. Docs remain at
  `lake_threads=1`, and literate extraction retains its independent `jobs`.
- `web_lake_threads` is recorded in the execution identity but is not a Web
  artifact input. The Web cache identity instead binds the branch/component,
  dependency manifest and toolchain, architecture, tooling and generator,
  generator inputs, and child `web_lean_threads`. A verified legacy cache can
  only seed a new schema namespace by copy followed by Lake trace validation;
  it is never relabelled in place.
- An orchestrator may describe a total CPU budget only when it controls and
  records all three layers: allocation/affinity, Lake workers, and child Lean
  workers. Logs and manifests must name the resolved values separately.
- Changing either stage's child-width field forks the relevant source/cache
  identity.
  Existing release caches are not rewritten in place. A new outer/inner
  profile must first be benchmarked on representative modules and introduced
  under a new cache identity when it changes trace inputs.
- Already frozen release tasks continue with their frozen tooling and
  checkpoints. Runtime tuning is not a reason to mutate an immutable tooling
  snapshot or abandon valid progress.
- A pre-allocation batch state may interpret a missing
  `instance_count_per_pod` only as the historical hard-coded value one. The
  coordinator accepts its old normalized-manifest digest only when the exact
  frozen normalization also matches, then records a reattach-only migration
  marker. Such a task may be polled by saved UUID but may not be restarted,
  retried, or newly created with an allocation-invalid shape.
- Full releases use a 172,800-second outer Verso default, while each literate
  batch retains its independent 7,200-second fail-fast deadline. Wiring
  canaries may explicitly choose a shorter outer timeout (never below the
  batch deadline plus shutdown grace).

## Alternatives considered

### Use `LAKE_JOBS` as the outer scheduler limit

Rejected because the supported Lake implementations do not read it. Logging
the variable created an audit trail that did not correspond to runtime
behavior.

### Force every child compiler to `-j 1` immediately

Rejected for existing caches because `-j` is a traced input. Although a wide
Lake pool with serial children is a useful profile to benchmark, imposing it
inside an in-progress release would invalidate otherwise reusable work.

### Set both Lake and Lean widths to the allocated vCPU count

Rejected as a default because it creates nested overcommit. A large-memory Pod
may survive that shape, but requested resources alone are not evidence that it
is faster.

### Keep one fixed profile for every stage

Rejected because branch compilation, literate extraction, documentation,
aggregation, and static publication expose different amounts of parallel
work. Resource defaults should follow measured stage behavior.

## Consequences

- A 16-vCPU finalizer can use all 16 CPUs during a Lake phase without
  pretending that its four validation workers or serial publication phases
  will do so.
- Resource logs are diagnostic: an operator can tell whether a slow run is
  allocation-bound, Lake-worker-bound, child-worker-bound,
  validation-worker-bound, or inherently serial.
- Cache reuse takes precedence over an unbenchmarked thread-profile change.
  Performance experiments use a new identity instead of contaminating the
  release cache.
- The SDK retains two explicit nested Lean scheduler dimensions plus a distinct
  post-Lake validation dimension. Callers must avoid multiplying the Lean
  widths accidentally and benchmark before raising any concurrency control.
- A 16-vCPU/Web-child-8 generated-site profile resolves to two outer Web jobs;
  a 16-vCPU/Web-child-16 profile resolves to one. Retrying with another outer width
  preserves compatible Web traces, while changing the child width forks the
  cache identity.
