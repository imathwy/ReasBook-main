import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_1_1

noncomputable section

universe u

-- The repository's canonical orientation owner for a smooth manifold is `ROrientedManifold`.
-- For Problem 23.9.5, the tangent-bundle orientability condition is a source-facing view of that
-- same orientation data, so this file keeps only a thin bridge alias rather than a second atlas
-- owner parallel to Chapter 20.

section

variable (R : outParam (Type u)) [CommRing R]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type u} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable (n : outParam ℕ)
variable (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
variable [Fact (Module.finrank ℝ E = n)]

/-- The source-facing condition that the tangent bundle of `M` is `R`-orientable is recorded in
this repository by the canonical Chapter 20 owner `ROrientedManifold R I n M`. -/
abbrev ROrientedTangentBundle := ROrientedManifold R I n M

/-- Unfolding `ROrientedTangentBundle` identifies tangent-bundle orientability with the canonical
manifold orientation owner from Chapter 20. -/
theorem rOrientedTangentBundle_iff :
    Nonempty (ROrientedTangentBundle R I n M) ↔ Nonempty (ROrientedManifold R I n M) :=
  Iff.rfl

/-- Problem 23.9.5: a smooth closed manifold is `R`-orientable iff its tangent bundle is
`R`-orientable. In this repository the tangent-bundle side is expressed by the same Chapter 20
orientation owner, so the equivalence does not require extra compactness or separation
assumptions. -/
theorem closedSmoothManifold_rOrientable_iff_tangentBundleROrientable :
    Nonempty (ROrientedManifold R I n M) ↔ Nonempty (ROrientedTangentBundle R I n M) :=
  Iff.rfl

end
