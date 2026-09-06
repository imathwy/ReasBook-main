# ADR-0010: Preserve theorem dependency provenance and isolate extraction

## Status

Accepted

## Date

2026-09-06

## Context

The generic theorem-map extractor reads compiled Lean environments and maps
declarations carrying literature labels to graph nodes. Its original call to
`ConstantInfo.getUsedConstantsAsSet` returned one set containing constants
from both `ConstantInfo.type` and the declaration value. For a theorem, those
are materially different claims: a type reference is part of the statement,
while a value reference is used by the proof. The single `dependencies` array
lost that provenance. Contracting unlabelled helper declarations then made it
impossible for a consumer to recover the distinction.

The original Python adapter also sent every project root to one Lean process.
Lean imported all roots into one shared `Environment`. This increased peak
memory with the size of a branch, and one import failure caused the generator
to discard successful compiled extraction for every sibling project and
silently replace all of them with source fallback. Source fallback recognizes
labels but does not elaborate Lean, so it always produces zero dependency
edges. An empty fallback graph was therefore easy to mistake for a valid
compiled result.

Compiled extraction and source discovery also have different inventory
boundaries. A valid `Book.lean` or `Paper.lean` aggregate can omit labelled
files that still belong to the review inventory, while elaboration can expose
labelled declarations that the lexical source scanner misses. Replacing one
inventory with the other therefore either hides reviewable statements or
discards compiled-only evidence.

ADR-0005 requires explicit control of nested Lean concurrency, and ADR-0006
establishes projects as independent failure and publication units. Theorem-map
extraction needs the same bounded project boundary.

## Decision

- The Lean extractor records three arrays per raw declaration:
  `statementDependencies` from constants in `ConstantInfo.type`,
  `proofDependencies` from the proof/value expression (including the existing
  structural handling for inductives, constructors, and recursors), and the
  backward-compatible `dependencies` union.
- Generated theorem-map schema version 2 carries the same two typed arrays on
  each literature-level item while retaining `dependencies` for version-1
  consumers.
- Dependency contraction starts from the selected statement or proof array,
  then follows the complete dependency union through unlabelled helpers until
  it reaches the nearest selected declarations. Thus the edge class describes
  where the dependency enters the reviewed declaration, even if the helper's
  internal path crosses its own type and body.
- The Python compiled-environment adapter invokes exactly one project per Lean
  process and processes projects serially. It never imports all books into one
  environment. Each invocation keeps the existing per-process timeout.
- A compiled failure falls back only for that project when fallback is
  enabled. Successful sibling results remain compiled. With fallback disabled,
  either an extraction error or missing compiled result fails closed.
- Generated evidence records a stable `fallbackReason` code. Source fallback
  continues to emit no dependency edges because lexical guesses are not
  equivalent to elaborated constant references.
- For a successful compiled project, the generator also builds a cheap source
  inventory and merges by stable literature item ID. Compiled records win on
  overlap; compiled-only records are appended; source-only records remain
  visible with empty dependency arrays and
  `dependencyEvidence: "source-only"`. No edge is inferred from source text.
- Generation metadata records compiled, source-only, compiled-only, and merged
  item counts plus `dependencyCoverage`. Consumers can distinguish complete,
  partial, and unavailable compiled coverage at both graph and item level.
- If a project aggregate root cannot compile, a release operator may build
  bounded temporary aggregates that import only non-empty project `.olean`
  files from the same immutable source commit and toolchain. Each chunk is
  extracted in its own Lean process. If independently compiled modules reuse
  a global Lean name and therefore cannot share an environment, the recovery
  greedily separates the conflicting import and retries the remaining group;
  a non-collision failure is bisected. Retries within one original group are
  serial, but independent original groups may run concurrently. The recovery
  accepts an explicit `jobs` limit of one through eight; every job has a
  unique aggregate module, output path, and temporary directory, while each
  Lean process retains the same timeout and `-j 1` thread limit.
- Only the coordinator writes the adaptive progress manifest, using atomic
  replacement after a whole original group succeeds. Worker processes write
  distinct compile logs, extraction logs, `.olean` roots, and pending raw JSON
  files. This lets one eight-instance pod keep up to eight independent Lean
  environments busy without concurrent mutation of the manifest or a shared
  output file.
- Dependency contraction happens inside each compatible Lean environment
  before results are merged by literature item ID. Repeated observations of
  the same source declaration must agree on display metadata, and their typed
  edge sets may be unioned. Helpers from incompatible environments are never
  merged by their ambiguous global name, so one standalone file cannot leak a
  dependency path into another. This recovery runs in a separate task after
  the failed build is terminal; it must not patch source files, overlap the
  source build, or mix artifacts from another commit.
- Partial output is marked `mode: "lean-environment-partial"`, records the
  available compiled module and total source-file counts, original and
  resolved chunk counts, collision-resolution mode, and originating build
  task, and is still overlaid on the complete source inventory. Only
  declarations actually observed in a successfully extracted environment
  receive compiled dependency edges.
- Curated theorem maps remain schema version 1 unless their owners explicitly
  adopt the typed contract. Existing consumers may continue to read the union
  field from either schema.

## Alternatives considered

### Infer dependency kinds from declaration names in the frontend

Rejected because names do not reveal whether a constant occurs in a theorem
statement or only in its proof. Once the extractor merges both sets, the
information is irrecoverable.

### Parse identifiers from source when compiled extraction fails

Rejected because notation, namespaces, local bindings, coercions, generated
declarations, and elaboration make lexical references unreliable. A
source-only graph may list statements, but it must not claim dependency edges.

### Import all roots once for throughput

Rejected as the release default because it couples failure domains and allows
branch size to determine peak memory. Project-isolated processes are slower to
start but bounded, diagnosable, and compatible with later externally
controlled project concurrency.

### Store only the two typed arrays

Rejected because existing theorem-map frontends and release metadata count the
legacy `dependencies` field. Keeping the union makes schema version 2
backward-compatible while new consumers adopt typed edges.

## Consequences

- Consumers can distinguish prerequisites visible in a proposition from
  lemmas used only to establish it, and can represent an edge that belongs to
  both classes.
- Peak extraction memory is bounded by the largest individual project rather
  than the union of every imported project environment.
- One broken book no longer erases valid dependency graphs for other books.
- Aggregate roots no longer make omitted labelled files disappear from the
  theorem-map inventory, and the UI does not present an isolated source-only
  node as proof that the declaration has no dependencies.
- A source-broken large project can expose sound dependencies for its compiled
  subset without claiming full coverage. The recovery costs another remote
  Lean import and remains bounded to one process with explicit metadata.
- Multi-project extraction pays one Lean startup cost per project. Any future
  parallelism must be explicit, externally bounded, and consistent with the
  two-level concurrency limits in ADR-0005.
- Previously published source-fallback maps still have zero edges and need a
  new compiled extraction before typed relationships can appear.
- Isolated group concurrency can use a multi-instance remote allocation while
  keeping each Lean environment single-threaded. Throughput is bounded by the
  slowest group and available memory rather than by the sum of every group,
  without changing the evidence merge semantics.
