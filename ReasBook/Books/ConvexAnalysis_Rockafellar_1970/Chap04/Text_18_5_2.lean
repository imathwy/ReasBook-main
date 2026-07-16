import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded

-- Declarations for this item will be appended below by the statement pipeline.

open Bornology

/-!
Source/core/bridge triage:

- Primary mathematical domain: extreme points of convex sets in finite-dimensional ordered
  normed spaces.
- `source-facing`: Text 18.5.2 records a 3-dimensional counterexample.
- `core/canonical`: this file keeps the source-level owner theorem at exact ambient
  dimension `Module.finrank ℝ E = 3`; compactness is exposed as a bridge consequence.
- owner abstractions: `IsClosed C`, `IsBounded C`,
  `Convex ℝ C`, and `Set.extremePoints ℝ C`.
- `bridge/view`: compactness upgrade from closed-bounded to compact in proper ambient spaces.

Domain-style sampling used here:
- `Set.extremePoints`, recalled as the owner for Definition 18.2 in `Chap04/Defn_18_2`;
- `mem_extremePoints`, the standard bridge theorem for pointwise use of that owner;
- `extremePoints_subset_closure_exposedPoints` from `Chap04/Theorem_18_6`,
  showing that the chapter's later extreme-point API continues to work directly with
  `C.extremePoints ℝ` and ordinary closure;
- `Metric.isCompact_of_isClosed_isBounded`, the canonical proper-space bridge used only for the
  compact companion below.

Primitive data vs derived API:
- primitive data: a set `C : Set E` in a finite-dimensional ambient normed space over `ℝ`
  with `Module.finrank ℝ E = 3`;
- source-facing properties: `IsClosed C`, `IsBounded C`, `Convex ℝ C`, and the failure
  of closedness for `C.extremePoints ℝ`;
- derived bridge properties: `IsCompact C` in proper spaces.

Layer target:
- the source-level exact-3 owner theorem is primary;
- the compact formulation is retained as a bridge view.
-/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Scalar-layer validation:
- the source item is intrinsically real (`ℝ³`) and this file keeps that scalar layer;
- normed-space/topological bridges (`IsBounded`/`IsCompact`) are used in the ambient space. -/

/-- Text 18.5.2, owner form: in every ambient real normed space with
`Module.finrank ℝ E = 3`, there exists a closed bounded convex set whose set of extreme points is
not closed. -/
-- Proof sketch: take the convex hull of the closed unit disk in the plane `z = 0` together with a
-- vertical segment through one of its boundary points. The resulting set is closed and bounded.
-- The two endpoints of the segment and every other boundary point of the disk are extreme, while
-- the distinguished boundary point is their limit but is not extreme because it lies in the
-- interior of the added segment.
theorem exists_isClosed_isBounded_convex_nonclosed_extremePoints
    (hE_dim : Module.finrank ℝ E = 3) :
    ∃ C : Set E, IsClosed C ∧ IsBounded C ∧ Convex ℝ C ∧ ¬ IsClosed (C.extremePoints ℝ) := sorry

/-- Proper-space bridge reformulation of Text 18.5.2: if the ambient metric space is proper, the
same counterexample is compact. -/
theorem exists_isCompact_convex_nonclosed_extremePoints_of_properSpace [ProperSpace E]
    (hE_dim : Module.finrank ℝ E = 3) :
    ∃ C : Set E, IsCompact C ∧ Convex ℝ C ∧ ¬ IsClosed (C.extremePoints ℝ) := by
  rcases exists_isClosed_isBounded_convex_nonclosed_extremePoints hE_dim with
    ⟨C, hC_closed, hC_bounded, hC_convex, hC_extremePoints⟩
  refine ⟨C, Metric.isCompact_of_isClosed_isBounded hC_closed hC_bounded,
    hC_convex, hC_extremePoints⟩

/-- Compact bridge form: every ambient real normed space with
`Module.finrank ℝ E = 3` admits a compact convex set whose extreme-point set is not closed. -/
theorem exists_isCompact_convex_nonclosed_extremePoints
    (hE_dim : Module.finrank ℝ E = 3) :
    ∃ C : Set E, IsCompact C ∧ Convex ℝ C ∧ ¬ IsClosed (C.extremePoints ℝ) := by
  have hE_pos : 0 < Module.finrank ℝ E := by
    simp [hE_dim]
  haveI : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos hE_pos
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  exact exists_isCompact_convex_nonclosed_extremePoints_of_properSpace hE_dim

end
