import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_20_4 (from Chap04) -/
open scoped Topology
open scoped Rockafellar

section Polytope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 20.4 inserts an intermediate polytope between a closed bounded convex
  set and one of its ambient-interior neighborhoods.
- `core/canonical`: the owner abstractions are `Set.IsPolytope`, `Convex ℝ`,
  the intrinsic neighborhood owner `nhdsSet`, and relative interior `ri[ℝ](·)`,
  `Metric.isCompact_of_isClosed_isBounded`, and
  `Convex.exists_subset_interior_convexHull_finset_of_isCompact`.
- `bridge/view`: a later polyhedral view of the resulting polytope belongs to the Chapter 19
  owner bridge and is not part of this file's source-facing public surface.
- Primitive data vs derived API: the primitive core inputs are the compact convex set `C`,
  an ambient neighborhood `D ∈ nhdsSet C`, and finite-dimensional real normed ambient data;
  `P.IsPolytope ℝ`, `P ∈ nhdsSet C`, and `P ⊆ D` are theorem-level outputs. The closed-bounded
  and ambient-interior forms are bridge corollaries.
- Domain-style sampling used here: `Set.IsPolytope`,
  `Metric.isCompact_of_isClosed_isBounded`,
  `nhdsSet`, `subset_interior_iff_mem_nhdsSet`, and
  `Convex.exists_subset_interior_convexHull_finset_of_isCompact`.
- Layer target: `core/canonical` on `Convex` with `nhdsSet`; the ambient-interior statement is a
  thin source-facing bridge, and the relative-interior (`ri`) theorem surfaces are the preferred
  intrinsic bridges. The scalar and ambient structure remain at the finite-dimensional
  real normed layer because the reused compact-convex interpolation owner currently lives there.
-/

namespace Convex

-- Proof sketch: apply mathlib's compact-convex interpolation theorem in the neighborhood-owner
-- form `D ∈ 𝓝ˢ C`; the finite witness gives a convex hull, then expose that hull through
-- the Chapter 1 owner `Set.IsPolytope`.
/-- Core owner form for Theorem 20.4: if `C` is compact and convex and `D` is a neighborhood of
`C`, then there is a polytope `P` with `P ∈ 𝓝ˢ C` and `P ⊆ D`. -/
theorem exists_polytope_mem_nhdsSet_subset
    {C D : Set E} (hC : Convex ℝ C) (hC_compact : IsCompact C) (hD_nhds : D ∈ 𝓝ˢ C) :
    ∃ P : Set E, P.IsPolytope ℝ ∧ P ∈ 𝓝ˢ C ∧ P ⊆ D := by
  rcases hC.exists_subset_interior_convexHull_finset_of_isCompact hC_compact hD_nhds with
    ⟨u, hC_sub, hP_sub⟩
  refine ⟨conv[ℝ] (u : Set E), ?_, ?_, hP_sub⟩
  · simpa using Set.IsPolytope.mk ℝ u.finite_toSet
  · rw [← subset_interior_iff_mem_nhdsSet]
    exact hC_sub

-- Proof sketch: combine Heine-Borel with the compact neighborhood-owner theorem above.
/-- Closed-bounded neighborhood bridge: if `C` is closed, bounded, and convex and `D` is a
neighborhood of `C`, then there exists a polytope `P` with `P ∈ 𝓝ˢ C` and `P ⊆ D`. -/
theorem exists_polytope_mem_nhdsSet_subset_of_isClosed_of_isBounded
    {C D : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C)
    (hC_bounded : Bornology.IsBounded C) (hD_nhds : D ∈ 𝓝ˢ C) :
    ∃ P : Set E, P.IsPolytope ℝ ∧ P ∈ 𝓝ˢ C ∧ P ⊆ D := by
  exact hC.exists_polytope_mem_nhdsSet_subset
    (Metric.isCompact_of_isClosed_isBounded hC_closed hC_bounded) hD_nhds

-- Proof sketch: convert `D ∈ 𝓝ˢ C` to `interior D ∈ 𝓝ˢ C`, then apply the neighborhood-owner
-- theorem to `interior D`.
theorem exists_polytope_mem_nhdsSet_subset_interior_of_isCompact
    {C D : Set E} (hC : Convex ℝ C) (hC_compact : IsCompact C) (hD_nhds : D ∈ 𝓝ˢ C) :
    ∃ P : Set E, P.IsPolytope ℝ ∧ P ∈ 𝓝ˢ C ∧ P ⊆ interior D := by
  have hInteriorD_nhds : interior D ∈ 𝓝ˢ C := by
    rw [← subset_interior_iff_mem_nhdsSet] at hD_nhds ⊢
    simpa [interior_interior] using hD_nhds
  exact hC.exists_polytope_mem_nhdsSet_subset hC_compact hInteriorD_nhds

-- Proof sketch: rewrite the intrinsic neighborhood-owner output `P ∈ nhdsSet C` as
-- `C ⊆ interior P`.
/-- Theorem 20.4, ambient-interior bridge form for compact sets: if `D` is a neighborhood of a
compact convex set `C`, then there exists a polytope `P` such that `C ⊆ interior P` and
`P ⊆ interior D`. -/
theorem exists_polytope_subset_interior_of_isCompact
    {C D : Set E} (hC : Convex ℝ C) (hC_compact : IsCompact C)
    (hD_nhds : D ∈ 𝓝ˢ C) :
    ∃ P : Set E, P.IsPolytope ℝ ∧ C ⊆ interior P ∧ P ⊆ interior D := by
  rcases hC.exists_polytope_mem_nhdsSet_subset_interior_of_isCompact hC_compact hD_nhds with
    ⟨P, hP_poly, hP_nhds, hP_sub⟩
  refine ⟨P, hP_poly, ?_, hP_sub⟩
  exact (subset_interior_iff_mem_nhdsSet).2 hP_nhds

/-- Intrinsic-right bridge form for compact sets: if `D` is a neighborhood of a compact convex
set `C`, then there exists a polytope `P` such that `C ⊆ ri[ℝ](P)` and `P ⊆ D`. -/
theorem exists_polytope_subset_ri_subset_of_isCompact
    {C D : Set E} (hC : Convex ℝ C) (hC_compact : IsCompact C)
    (hD_nhds : D ∈ 𝓝ˢ C) :
    ∃ P : Set E, P.IsPolytope ℝ ∧ C ⊆ ri[ℝ](P) ∧ P ⊆ D := by
  rcases hC.exists_polytope_mem_nhdsSet_subset hC_compact hD_nhds with
    ⟨P, hP_poly, hP_nhds, hPD⟩
  exact ⟨P, hP_poly,
    ((subset_interior_iff_mem_nhdsSet).2 hP_nhds).trans interior_subset_intrinsicInterior,
    hPD⟩

/-- Relative-interior bridge form for compact sets: if `D` is a neighborhood of a compact convex
set `C`, then there exists a polytope `P` such that `C ⊆ ri[ℝ](P)` and `P ⊆ ri[ℝ](D)`. -/
theorem exists_polytope_subset_ri_of_isCompact
    {C D : Set E} (hC : Convex ℝ C) (hC_compact : IsCompact C)
    (hD_nhds : D ∈ 𝓝ˢ C) :
    ∃ P : Set E, P.IsPolytope ℝ ∧ C ⊆ ri[ℝ](P) ∧ P ⊆ ri[ℝ](D) := by
  have hInteriorD_nhds : interior D ∈ 𝓝ˢ C := by
    rw [← subset_interior_iff_mem_nhdsSet] at hD_nhds ⊢
    simpa [interior_interior] using hD_nhds
  rcases hC.exists_polytope_subset_ri_subset_of_isCompact hC_compact hInteriorD_nhds with
    ⟨P, hP_poly, hCP, hPD⟩
  exact ⟨P, hP_poly, hCP, hPD.trans interior_subset_intrinsicInterior⟩

-- Proof sketch: `C ⊆ interior D` is exactly `D ∈ nhdsSet C`.
/-- Theorem 20.4, ambient-interior bridge form for compact sets: if a compact convex set `C` lies
in the interior of `D`, then there exists a polytope `P` such that `C ⊆ interior P` and
`P ⊆ interior D`. -/
theorem exists_polytope_subset_interior_of_isCompact_of_subset_interior
    {C D : Set E} (hC : Convex ℝ C) (hC_compact : IsCompact C) (hCD : C ⊆ interior D) :
    ∃ P : Set E, P.IsPolytope ℝ ∧ C ⊆ interior P ∧ P ⊆ interior D := by
  have hD_nhds : D ∈ 𝓝ˢ C := by
    rwa [← subset_interior_iff_mem_nhdsSet]
  exact hC.exists_polytope_subset_interior_of_isCompact hC_compact hD_nhds

/-- Relative-interior bridge for compact sets under ambient interior inclusion: if `C` is compact
convex and `C ⊆ interior D`, then there exists a polytope `P` with
`C ⊆ ri[ℝ](P)` and `P ⊆ ri[ℝ](D)`. -/
theorem exists_polytope_subset_ri_of_isCompact_of_subset_interior
    {C D : Set E} (hC : Convex ℝ C) (hC_compact : IsCompact C) (hCD : C ⊆ interior D) :
    ∃ P : Set E, P.IsPolytope ℝ ∧ C ⊆ ri[ℝ](P) ∧ P ⊆ ri[ℝ](D) := by
  have hD_nhds : D ∈ 𝓝ˢ C := by
    rwa [← subset_interior_iff_mem_nhdsSet]
  exact hC.exists_polytope_subset_ri_of_isCompact hC_compact hD_nhds

-- Proof sketch: combine Heine-Borel with the compact intrinsic-neighborhood theorem above.
theorem exists_polytope_mem_nhdsSet_subset_interior_of_isClosed_of_isBounded
    {C D : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C)
    (hC_bounded : Bornology.IsBounded C) (hD_nhds : D ∈ 𝓝ˢ C) :
    ∃ P : Set E, P.IsPolytope ℝ ∧ P ∈ 𝓝ˢ C ∧ P ⊆ interior D := by
  exact hC.exists_polytope_mem_nhdsSet_subset_interior_of_isCompact
    (Metric.isCompact_of_isClosed_isBounded hC_closed hC_bounded) hD_nhds

/-- Closed-bounded ambient-interior bridge form: if `D` is a neighborhood of a closed bounded
convex set `C`, then there exists a polytope `P` such that `C ⊆ interior P` and
`P ⊆ interior D`. -/
theorem exists_polytope_subset_interior_of_isClosed_of_isBounded
    {C D : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C)
    (hC_bounded : Bornology.IsBounded C) (hD_nhds : D ∈ 𝓝ˢ C) :
    ∃ P : Set E, P.IsPolytope ℝ ∧ C ⊆ interior P ∧ P ⊆ interior D := by
  rcases hC.exists_polytope_mem_nhdsSet_subset_interior_of_isClosed_of_isBounded
      hC_closed hC_bounded hD_nhds with ⟨P, hP_poly, hP_nhds, hP_sub⟩
  exact ⟨P, hP_poly, (subset_interior_iff_mem_nhdsSet).2 hP_nhds, hP_sub⟩

/-- Closed-bounded intrinsic-right bridge form: if `D` is a neighborhood of a closed bounded
convex set `C`, then there exists a polytope `P` such that `C ⊆ ri[ℝ](P)` and
`P ⊆ D`. -/
theorem exists_polytope_subset_ri_subset_of_isClosed_of_isBounded
    {C D : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C)
    (hC_bounded : Bornology.IsBounded C) (hD_nhds : D ∈ 𝓝ˢ C) :
    ∃ P : Set E, P.IsPolytope ℝ ∧ C ⊆ ri[ℝ](P) ∧ P ⊆ D := by
  exact hC.exists_polytope_subset_ri_subset_of_isCompact
    (Metric.isCompact_of_isClosed_isBounded hC_closed hC_bounded) hD_nhds

/-- Closed-bounded relative-interior bridge form: if `D` is a neighborhood of a closed bounded
convex set `C`, then there exists a polytope `P` such that `C ⊆ ri[ℝ](P)` and
`P ⊆ ri[ℝ](D)`. -/
theorem exists_polytope_subset_ri_of_isClosed_of_isBounded
    {C D : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C)
    (hC_bounded : Bornology.IsBounded C) (hD_nhds : D ∈ 𝓝ˢ C) :
    ∃ P : Set E, P.IsPolytope ℝ ∧ C ⊆ ri[ℝ](P) ∧ P ⊆ ri[ℝ](D) := by
  have hInteriorD_nhds : interior D ∈ 𝓝ˢ C := by
    rw [← subset_interior_iff_mem_nhdsSet] at hD_nhds ⊢
    simpa [interior_interior] using hD_nhds
  rcases hC.exists_polytope_subset_ri_subset_of_isClosed_of_isBounded
      hC_closed hC_bounded hInteriorD_nhds with ⟨P, hP_poly, hCP, hPD⟩
  exact ⟨P, hP_poly, hCP, hPD.trans interior_subset_intrinsicInterior⟩

/-- Theorem 20.4, ambient-interior bridge form for closed bounded sets: if a closed bounded convex
set `C` lies in the interior of
a set `D` in a finite-dimensional real normed space, then there exists a polytope `P` such that
`C ⊆ interior P` and `P ⊆ interior D`. -/
-- Proof sketch: apply the compact owner bridge above after converting the closed bounded set `C`
-- into a compact set by Heine-Borel, then specialize to the ambient-interior neighborhood.
theorem exists_polytope_subset_interior_of_isClosed_of_isBounded_of_subset_interior
    {C D : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C)
    (hC_bounded : Bornology.IsBounded C) (hCD : C ⊆ interior D) :
    ∃ P : Set E, P.IsPolytope ℝ ∧ C ⊆ interior P ∧ P ⊆ interior D := by
  have hD_nhds : D ∈ 𝓝ˢ C := by
    rwa [← subset_interior_iff_mem_nhdsSet]
  exact hC.exists_polytope_subset_interior_of_isClosed_of_isBounded
    hC_closed hC_bounded hD_nhds

/-- Closed-bounded relative-interior bridge under ambient interior inclusion: if `C` is closed,
bounded, convex, and `C ⊆ interior D`, then there exists a polytope `P` with
`C ⊆ ri[ℝ](P)` and `P ⊆ ri[ℝ](D)`. -/
theorem exists_polytope_subset_ri_of_isClosed_of_isBounded_of_subset_interior
    {C D : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C)
    (hC_bounded : Bornology.IsBounded C) (hCD : C ⊆ interior D) :
    ∃ P : Set E, P.IsPolytope ℝ ∧ C ⊆ ri[ℝ](P) ∧ P ⊆ ri[ℝ](D) := by
  have hD_nhds : D ∈ 𝓝ˢ C := by
    rwa [← subset_interior_iff_mem_nhdsSet]
  exact hC.exists_polytope_subset_ri_of_isClosed_of_isBounded
    hC_closed hC_bounded hD_nhds

end Convex

end Polytope
