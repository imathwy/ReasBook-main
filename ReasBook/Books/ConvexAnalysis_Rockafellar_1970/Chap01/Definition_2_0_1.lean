import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Definition 2.0.1 introduces convex subsets by closure under strict convex
  combinations `(1 - λ) x + λ y` for `0 < λ < 1`.
- `core/canonical`: the owner abstraction in mathlib is `Convex 𝕜 C`.
- `bridge/view`: primitive bridges are `convex_iff_segment_subset` (segment owner view) and
  `convex_iff_add_mem` (nonnegative affine-combination view at the weaker `SMul` layer), together
  with the set-level pointwise bridge `convex_iff_pointwise_add_subset` / `Convex.set_combo_subset`
  that avoids elementwise coefficient/coercion noise on theorem surfaces. The textbook
  strict-inequality formulation is the standard derived characterization `convex_iff_forall_pos`;
  its intrinsic owner-level coefficient form is `convex_iff_pairwise_pos`; the strict geometric
  form uses open segments via `convex_iff_openSegment_subset`, and owner-level
  open-segment closure is exposed by `Convex.openSegment_subset`.
- Domain-style sampling used here: `Convex`, `Convex.starConvex`, `convex_iff_segment_subset`,
  `convex_iff_add_mem`, `convex_iff_pointwise_add_subset`, `Convex.set_combo_subset`,
  `convex_iff_forall_pos`, `convex_iff_pairwise_pos`, `openSegment`,
  `convex_iff_openSegment_subset`,
  `Convex.segment_subset`, and `Convex.openSegment_subset`.
- Primitive data vs derived API: `Convex` is the primitive owner notion, and
  `Convex.starConvex` is its direct owner projection; the segment criterion and nonnegative
  affine-combination criteria (both elementwise and pointwise-set forms) are primitive bridge API
  at the canonical layer, while strict-coefficient and open-segment forms (including the intrinsic
  pairwise strict-coefficient bridge) are derived bridge API and should stay thin bridge theorems
  rather than parallel local owners.
- Layer target: `core/canonical`, with the source phrasing retained by canonical bridge theorems.

Abstraction audit (canonicalize):
- Codomain/ambient layer over-concrete? `No`: `Convex` is codomain-free and already at the
  canonical set/module owner layer.
- Scalar/ambient structure stronger than needed? `No`: the coefficient bridge is exposed at the
  weaker `SMul` layer via `convex_iff_add_mem`; strict-coefficient and open-segment forms are
  retained only as derived source-facing views.
- Owner tied to a concrete model? `No`: the owner is the intrinsic predicate `Convex 𝕜`.
- Ambient-vs-intrinsic topology mismatch? `No`: this surface avoids ambient closure/interior
  language entirely and uses affine-segment bridge theorems at the owner layer.
- Owner name/notation too heavy or too concrete? `No`: short canonical owner names are used
  directly (`Convex`, `Convex.openSegment_subset`) without local synonym wrappers.
- Need notation on theorem surfaces? `No extra notation needed`: existing segment/open-segment
  notation (`[x -[𝕜] y]`, `]x -[𝕜] y[`) already expresses the source-facing geometry.
-/

/- Definition 2.0.1: a subset is convex in the canonical mathlib sense of `Convex`,
meaning it contains every convex combination (hence in particular every strict convex
combination) of two of its points. -/
recall Convex

/- Direct owner bridge: from `x ∈ C`, convexity gives star-convexity of `C` at the center `x`.
This is the primitive elimination principle of the owner. -/
recall Convex.starConvex

/- Primitive bridge to the owner: convexity is exactly closure under all closed segments
`[x -[𝕜] y]` between points of the set. -/
recall convex_iff_segment_subset

/- Primitive coefficient bridge at the weaker abstraction layer: convexity is closure under all
nonnegative affine combinations `a • x + b • y` with `a + b = 1`. -/
recall convex_iff_add_mem

/- Primitive pointwise-set bridge at the same weak owner layer: convexity is equivalent to closure
under pointwise convex combinations `a • C + b • C` when `a,b ≥ 0` and `a + b = 1`. -/
recall convex_iff_pointwise_add_subset

/- Owner elimination in pointwise form: from convexity, each admissible pointwise convex
combination of the set is contained in the set. -/
recall Convex.set_combo_subset

/- The textbook formula `(1 - λ) x + λ y` with `0 < λ < 1` is the standard positive-coefficient
characterization of `Convex`. -/
recall convex_iff_forall_pos

/- Intrinsic strict-coefficient bridge on the owner itself: convexity is equivalent to pairwise
closure under positive affine combinations. -/
recall convex_iff_pairwise_pos

/- Source-facing strict-combination owner object: open segments `]x -[𝕜] y[` are the intrinsic
set-level strict interpolation surface. -/
recall openSegment

/- Intrinsic strict bridge: convexity is equivalent to closure under open segments. -/
recall convex_iff_openSegment_subset

/- Source-facing direct owner theorem: closed-segment membership is available from the owner
without introducing a chapter-local wrapper. -/
recall Convex.segment_subset

/- Source-facing direct owner theorem: membership in open segments is available without introducing
a parallel chapter-local wrapper. -/
recall Convex.openSegment_subset
