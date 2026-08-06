import Mathlib.Topology.Homotopy.HSpaces
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Adjunction_8_2_6

open scoped unitInterval

noncomputable section

universe u v w

/-- Construction 8.2.7: under the suspension-loop adjunction
`F(ΣX, Y) ≃ F(X, ΩY)`, the sum corresponding to based maps `f, g : ΣX → Y` is the based map
`X → ΩY` obtained by pointwise concatenating their adjoint loops. -/
def suspensionMapAdd
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (f g : PointedCompactlyGenerated.basedMappingSpace (Σ X) Y) :
    PointedCompactlyGenerated.basedMappingSpace X (Ω Y) :=
  let f' : PointedCompactlyGenerated.basedMappingSpace X (Ω Y) :=
    suspensionLoopAdjunctionHomeomorph X Y f
  let g' : PointedCompactlyGenerated.basedMappingSpace X (Ω Y) :=
    suspensionLoopAdjunctionHomeomorph X Y g
  { toContinuousMap :=
      { toFun := fun x ↦
          (f' x).trans (g' x)
        continuous_toFun := by
          exact continuous_loopPointedSpace_trans Y f'.continuous g'.continuous }
    map_zero' := by
      have hf : f' X.point = (Ω Y).point := map_zero f'
      have hg : g' X.point = (Ω Y).point := map_zero g'
      change (f' X.point).trans (g' X.point) = (Ω Y).point
      rw [hf, hg]
      simp }

/-- Evaluating `suspensionMapAdd X Y f g` at `x` gives the concatenation of the two adjoint loops
coming from `f` and `g`. -/
@[simp] theorem suspensionMapAdd_apply
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (f g : PointedCompactlyGenerated.basedMappingSpace (Σ X) Y)
    (x : X.toCompactlyGenerated) :
    suspensionMapAdd X Y f g x =
      (suspensionLoopAdjunctionHomeomorph X Y f x).trans
        (suspensionLoopAdjunctionHomeomorph X Y g x) :=
  rfl

/-- Pointwise, the loop corresponding to `suspensionMapAdd X Y f g` traverses first the meridian
loop induced by `f` and then the one induced by `g`. -/
@[simp] theorem suspensionMapAdd_apply_eval
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w})
    (f g : PointedCompactlyGenerated.basedMappingSpace (Σ X) Y)
    (x : X.toCompactlyGenerated) (t : I) :
    suspensionMapAdd X Y f g x t =
      ((suspensionLoopAdjunctionHomeomorph X Y f x).trans
        (suspensionLoopAdjunctionHomeomorph X Y g x)) t :=
  rfl
