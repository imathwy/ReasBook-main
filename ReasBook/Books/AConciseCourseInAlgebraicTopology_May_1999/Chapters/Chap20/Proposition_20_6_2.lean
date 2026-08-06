import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_6_2.Covering
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3

open Bundle CategoryTheory
open scoped Manifold Topology

noncomputable section

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

namespace OrientationCover

section Manifold

variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
variable [Fact (Module.finrank ℝ E = n)]

/-- Proposition 20.6.2 (1) (covering-space clause). The orientation-cover projection is a
two-fold cover: over every `x : M`, an evenly covered neighborhood has model fiber `ℤˣ`. -/
theorem isEvenlyCovered_projection [ConnectedSpace M] (x : M) :
    IsEvenlyCovered (projection : OrientationCover n M → M) x ℤˣ := by
  rcases existsLocalTopHomologyTrivializationAt x with ⟨U, hxU⟩
  exact isEvenlyCovered_projection_of_mem_domain U hxU

/-- Proposition 20.6.2 (2) (connectedness clause). For a connected `n`-manifold, the orientation
cover is connected exactly when its projection has no global continuous section. This is the
covering-space formulation of nonorientability and does not identify arbitrary unit-compatible
local charts with a choice of orientation. -/
theorem connectedSpace_iff_nonorientable [ConnectedSpace M]
    [I.Boundaryless] :
    ConnectedSpace (OrientationCover n M) ↔
      ¬ ∃ s : C(M, OrientationCover n M),
        projection ∘ s = fun x ↦ x :=
  connectedSpace_iff_noContinuousSection (I := I) (n := n) (M := M)

end Manifold

end OrientationCover

end
