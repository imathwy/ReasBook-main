import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3
import Mathlib.LinearAlgebra.FreeModule.Basic

open scoped Manifold Topology

noncomputable section

-- Semantic recall: Chapter 20 already exposes `rSingularHomology` as the canonical constant-
-- coefficient singular homology owner, while `ROrientedManifold` remains the chapter-local
-- orientability owner.

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
variable [ConnectedSpace M] [CompactSpace M]
variable {n : ℕ} [Fact (Module.finrank ℝ E = n)]

/-- Problem 20.7.3: under the standing compact connected boundaryless `n`-manifold hypotheses,
if `M` is orientable, then `H_(n - 1)(M; ℤ)` is a free Abelian group. The chapter-local
orientability owner is `ROrientedManifold`, and the chapter-local homology owner is
`rSingularHomology`. -/
theorem integralSingularHomology_free_of_orientableManifold
    (hn : 0 < n) (h_orientable : Nonempty (ROrientedManifold ℤ I n M)) :
    Module.Free ℤ (rSingularHomology ℤ (n - 1) (TopCat.of M)) := sorry

end
