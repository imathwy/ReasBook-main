import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_6_2
import Mathlib.Topology.Homotopy.Lifting

open scoped Manifold Topology

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
variable [Fact (Module.finrank ℝ E = n)]

namespace OrientationCover

/-- The fiber of the canonical projection `OrientationCover.projection : OrientationCover n M → M`
over `x` is exactly the space of local orientations at `x`. -/
def fiberEquivLocalOrientation (x : M) :
    {y : OrientationCover n M // projection y = x} ≃ LocalOrientation n x where
  toFun y := by
    rcases y with ⟨⟨x, α⟩, rfl⟩
    exact α
  invFun α := ⟨⟨x, α⟩, rfl⟩
  left_inv y := by
    rcases y with ⟨⟨x, α⟩, rfl⟩
    rfl
  right_inv α := rfl

@[simp] theorem fiberEquivLocalOrientation_apply_mk (x : M) (α : LocalOrientation n x) :
    fiberEquivLocalOrientation x ⟨⟨x, α⟩, rfl⟩ = α :=
  rfl

@[simp] theorem fiberEquivLocalOrientation_symm_apply (x : M) (α : LocalOrientation n x) :
    (fiberEquivLocalOrientation x).symm α = ⟨⟨x, α⟩, rfl⟩ :=
  rfl

/-- Remark 20.6.4: once Proposition 20.6.2 equips `OrientationCover n M` with its canonical
covering-space structure, the fiber of the resulting monodromy functor over `x : M` is exactly the
space of local orientations at `x`. -/
abbrev monodromyFiberEquivLocalOrientation (x : M) :
    let cov : IsCoveringMap (projection : OrientationCover n M → M) := isCoveringMap_projection
    cov.monodromyFunctor.obj (FundamentalGroupoid.mk x) ≃
      LocalOrientation n x :=
  fiberEquivLocalOrientation x

end OrientationCover

end

/- Remark 20.6.4: Proposition 20.6.2 now equips `OrientationCover n M` with its canonical
sheet-generated topology `OrientationCover.topology` and proves that the canonical projection
`OrientationCover.projection : OrientationCover n M → M` is a covering map. Therefore the
orientation cover already fits the canonical monodromy formalism:
`OrientationCover.isCoveringMap_projection.monodromyFunctor` controls transport in the fibers of
`OrientationCover.projection`, and `OrientationCover.monodromyFiberEquivLocalOrientation`
identifies those fibers with the local orientation spaces `LocalOrientation n x`. At a basepoint
`x`, the corresponding automorphism action is governed by `FundamentalGroup M x`. -/
#check OrientationCover.topology
#check OrientationCover.projection
#check OrientationCover.isCoveringMap_projection
#check OrientationCover.monodromyFiberEquivLocalOrientation
#check IsCoveringMap.monodromyFunctor
#check FundamentalGroup
