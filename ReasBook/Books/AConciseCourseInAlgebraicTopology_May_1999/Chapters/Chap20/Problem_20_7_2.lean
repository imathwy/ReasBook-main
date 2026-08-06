import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_6_2

open scoped Manifold

noncomputable section

section

variable {H : Type} [TopologicalSpace H]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable {n : ℕ} [Fact (Module.finrank ℝ E = n)]
variable [LieGroup I ⊤ G]

-- Semantic recall: local search verified the chapter owner `ROrientedManifold` in
-- `Definition_20_1_1`. The source problem is therefore expressed by existence of that orientation
-- structure, but in the stronger canonical Lie-group form since compactness and connectedness do
-- not affect orientability here.

/-- Helper for Problem 20.7.2: a covering family of pairwise compatible local top-homology
trivializations determines an `ROrientedManifold ℤ I n G`. -/
theorem nonempty_rOrientedManifold_of_coveringFamily
    (atlasFamily : G → LocalTopHomologyTrivialization ℤ n G)
    (hmem : ∀ g : G, g ∈ (atlasFamily g).domain)
    (hcompat : ∀ g h : G,
      (atlasFamily g).OrientationCompatible (atlasFamily h)) :
    Nonempty (ROrientedManifold ℤ I n G) := by
  -- Package the given family into the atlas `Set.range atlasFamily`.
  refine ⟨(show ROrientedManifold ℤ I n G from {
    toIsManifold := inferInstance
    atlas := Set.range atlasFamily
    cover := ?_
    pairwise_compatible := ?_ })⟩
  · intro g
    exact ⟨atlasFamily g, ⟨g, rfl⟩, hmem g⟩
  · intro U V hU hV
    rcases hU with ⟨g, rfl⟩
    rcases hV with ⟨h, rfl⟩
    exact hcompat g h

/-- Problem 20.7.2: a Lie group is orientable, hence in particular every compact connected Lie
group is orientable. In the chapter-local API this is formalized as the existence of an
`ROrientedManifold ℤ I n G` structure, where `Fact (Module.finrank ℝ E = n)` supplies the
manifold dimension. -/
theorem compactConnectedLieGroup_orientable :
    Nonempty (ROrientedManifold ℤ I n G) := by
  -- A genuine proof must transport one orientation at the identity by left translations. Merely
  -- choosing arbitrary local manifold charts only gives unit-compatible charts and cannot choose
  -- their signs coherently.
  sorry

end
