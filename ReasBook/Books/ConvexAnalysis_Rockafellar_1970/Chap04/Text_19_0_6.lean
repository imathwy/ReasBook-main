import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_4

-- Declarations for this item will be appended below by the statement pipeline.

section

open Bornology Set
open scoped Rockafellar

variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [Bornology E] [AddCommMonoid E] [Module 𝕜 E]

/-!
Source/core/bridge triage:
- `source-facing`: Text 19.0.6 singles out the unbounded finitely generated case and interprets
  the finite direction generators as vertices at infinity.
- `core/canonical`: the chapter owner remains `Set.IsFinitelyGeneratedConvex`, built from
  `mixedConvexHull`, `ray`, and `Set.Finite`.
- `bridge/view`: the right refinement is a thin theorem saying that an unbounded finitely
  generated convex set admits a mixed-hull presentation by finitely many points together with a
  nonempty finite family of direction rays.

Domain-style sampling used here:
- `Set.IsFinitelyGeneratedConvex`;
- `mixedConvexHull`;
- `mem_ray_iff`;
- `mixedConvexHull_eq_convexHull_of_directions_subset_zero`;
- `Set.Finite.isCompact_convexHull`.

Primitive data vs derived API:
- primitive owner data: finite generating points and finite generating direction rays carried by
  `Set.IsFinitelyGeneratedConvex`;
- primitive ambient bridge input: boundedness of the specific point-generator convex hull;
- derived bridge data here: when the set is unbounded, the direction family cannot be empty, since
  the empty-direction case collapses to a bounded finite convex hull.

Layer target: `bridge/view`.

Ambient refinement:
- core owner theorem below is stated on the weakest bornological module layer plus the primitive
  bridge assumption that the relevant point convex hull is bounded, and a thin derived wrapper then
  recovers the finite-family boundedness bridge input;
- the source-facing topological specialization is then recovered as a thin bridge theorem using
  `Set.Finite.isCompact_convexHull` and `IsCompact.isBounded`.
-/

namespace Set.IsFinitelyGeneratedConvex

/-- Primitive mixed-hull layer: if the point-generator convex hull is bounded, then an unbounded
mixed convex hull must have a nonempty direction-ray family. -/
theorem directions_nonempty_of_not_isBounded_mixedConvexHull_of_isBounded_convexHull
    {points : Set E} {directions : Set (Module.Ray 𝕜 E)}
    (hbounded_convexHull_points : IsBounded (conv[𝕜] points))
    (hunbounded : ¬ IsBounded (mconv[𝕜](points | ray directions))) :
    directions.Nonempty := by
  by_contra hdirections_empty
  have hray_zero : ray directions ⊆ ({0} : Set E) := by
    intro y hy
    rcases (mem_ray_iff directions y).1 hy with rfl | ⟨_, hy_direction⟩
    · simp
    · exact (hdirections_empty ⟨_, hy_direction⟩).elim
  have hbounded_mixed : IsBounded (mconv[𝕜](points | ray directions)) := by
    rw [mixedConvexHull_eq_convexHull_of_directions_subset_zero 𝕜 hray_zero]
    exact hbounded_convexHull_points
  exact hunbounded hbounded_mixed

/-- Derived finite-generator bridge: if all finite point-generator convex hulls are bounded, then
an unbounded finite-point mixed convex hull must have a nonempty direction-ray family. -/
theorem directions_nonempty_of_not_isBounded_mixedConvexHull_of_bounded_convexHull_finite
    {points : Set E} {directions : Set (Module.Ray 𝕜 E)}
    (hpoints_finite : points.Finite)
    (hbounded_convexHull_finite : ∀ {s : Set E}, s.Finite → IsBounded (conv[𝕜] s))
    (hunbounded : ¬ IsBounded (mconv[𝕜](points | ray directions))) :
    directions.Nonempty :=
  directions_nonempty_of_not_isBounded_mixedConvexHull_of_isBounded_convexHull
    (hbounded_convexHull_finite hpoints_finite) hunbounded

/-- Text 19.0.6, core owner form: assuming finite convex hulls are bounded, an unbounded finitely
generated convex set admits a finite mixed presentation by points together with a nonempty finite
family of direction rays (the source's vertices at infinity). -/
theorem exists_points_directions_of_not_isBounded_of_bounded_convexHull_finite {C : Set E}
    (hC : C.IsFinitelyGeneratedConvex 𝕜)
    (hbounded_convexHull_finite : ∀ {s : Set E}, s.Finite → IsBounded (conv[𝕜] s))
    (hC_unbounded : ¬ IsBounded C) :
    ∃ points : Set E, ∃ directions : Set (Module.Ray 𝕜 E),
      points.Finite ∧ directions.Finite ∧ directions.Nonempty ∧
        C = mconv[𝕜](points | ray directions) := by
  rcases hC with ⟨points, directions, hpoints_finite, hdirections_finite, hC_eq⟩
  refine ⟨points, directions, hpoints_finite, hdirections_finite, ?_, hC_eq⟩
  refine directions_nonempty_of_not_isBounded_mixedConvexHull_of_bounded_convexHull_finite
    hpoints_finite hbounded_convexHull_finite ?_
  simpa [hC_eq] using hC_unbounded

end Set.IsFinitelyGeneratedConvex

end

section

open Bornology Set
open scoped Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderClosedTopology 𝕜] [CompactIccSpace 𝕜] [ContinuousAdd 𝕜]
variable {E : Type*} [TopologicalSpace E] [Bornology E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

namespace Set.IsFinitelyGeneratedConvex

/-- Topological-boundedness bridge form of Text 19.0.6: if compact sets are bounded in the ambient
bornology, then an unbounded finite-point mixed convex hull has a nonempty direction family. -/
theorem directions_nonempty_of_not_isBounded_mixedConvexHull_of_isCompact_isBounded
    {points : Set E} {directions : Set (Module.Ray 𝕜 E)}
    (hpoints_finite : points.Finite)
    (hcompact_isBounded : ∀ {s : Set E}, IsCompact s → IsBounded s)
    (hunbounded : ¬ IsBounded (mconv[𝕜](points | ray directions))) :
    directions.Nonempty := by
  refine directions_nonempty_of_not_isBounded_mixedConvexHull_of_isBounded_convexHull ?_ hunbounded
  exact hcompact_isBounded (hpoints_finite.isCompact_convexHull 𝕜)

/-- Topological-boundedness bridge form of Text 19.0.6: if compact sets are bounded in the ambient
bornology, an unbounded finitely generated convex set admits a finite mixed presentation by points
together with a nonempty finite family of direction rays. -/
theorem exists_points_directions_of_not_isBounded_of_isCompact_isBounded {C : Set E}
    (hC : C.IsFinitelyGeneratedConvex 𝕜)
    (hcompact_isBounded : ∀ {s : Set E}, IsCompact s → IsBounded s)
    (hC_unbounded : ¬ IsBounded C) :
    ∃ points : Set E, ∃ directions : Set (Module.Ray 𝕜 E),
      points.Finite ∧ directions.Finite ∧ directions.Nonempty ∧
        C = mconv[𝕜](points | ray directions) := by
  exact
    exists_points_directions_of_not_isBounded_of_bounded_convexHull_finite
      hC (fun hs ↦ hcompact_isBounded (hs.isCompact_convexHull 𝕜)) hC_unbounded

end Set.IsFinitelyGeneratedConvex

end

section

open Bornology Set
open scoped Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderClosedTopology 𝕜] [CompactIccSpace 𝕜] [ContinuousAdd 𝕜]
variable {E : Type*} [PseudoMetricSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

namespace Set.IsFinitelyGeneratedConvex

/-- Source-facing bridge form of Text 19.0.6: in the standard metric-topological ambient where
finite convex hulls are compact (hence bounded), an unbounded finite-point mixed convex hull has a
nonempty direction family. -/
theorem directions_nonempty_of_not_isBounded_mixedConvexHull
    {points : Set E} {directions : Set (Module.Ray 𝕜 E)}
    (hpoints_finite : points.Finite)
    (hunbounded : ¬ IsBounded (mconv[𝕜](points | ray directions))) :
    directions.Nonempty :=
  directions_nonempty_of_not_isBounded_mixedConvexHull_of_isCompact_isBounded
    hpoints_finite (fun hs ↦ hs.isBounded) hunbounded

/-- Text 19.0.6, source-facing bridge form: in the standard metric-topological ambient, an
unbounded finitely generated convex set admits a finite mixed presentation by points together with
a nonempty finite family of direction rays, interpreted as vertices at infinity. -/
theorem exists_points_directions_of_not_isBounded {C : Set E}
    (hC : C.IsFinitelyGeneratedConvex 𝕜) (hC_unbounded : ¬ IsBounded C) :
    ∃ points : Set E, ∃ directions : Set (Module.Ray 𝕜 E),
      points.Finite ∧ directions.Finite ∧ directions.Nonempty ∧
        C = mconv[𝕜](points | ray directions) :=
  exists_points_directions_of_not_isBounded_of_isCompact_isBounded
    hC (fun hs ↦ hs.isBounded) hC_unbounded

end Set.IsFinitelyGeneratedConvex

end
