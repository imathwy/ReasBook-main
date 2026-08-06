import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Construction_6_2_2

open ContinuousMap
open scoped unitInterval

-- Semantic recall: the canonical Chapter 6 owner for the mapping cylinder of a continuous map
-- is `ContinuousMap.mappingCylinder`; this item adds the source-facing factorization maps
-- `X ⟶ M_f ⟶ Y`.

noncomputable section

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The canonical map `X ⟶ M_f` obtained by sending `x` to the class of `(x, 0)` in the mapping
cylinder of `f`. -/
def mappingCylinderIn (f : C(X, Y)) : C(X, f.mappingCylinder) :=
  (mappingCylinderCylinderInclusion f).comp (mappingCylinderTimeZeroInclusion X)

/-- The canonical projection `M_f ⟶ Y` induced by collapsing the cylinder direction. -/
def mappingCylinderProjection (f : C(X, Y)) : C(f.mappingCylinder, Y) :=
  mappingCylinderDesc (ContinuousMap.id Y) (ContinuousMap.Homotopy.refl f)

/-- The canonical projection `M_f ⟶ Y` restricts on the target inclusion `Y ⟶ M_f` to the
identity of `Y`. -/
theorem mappingCylinderProjection_comp_targetInclusion (f : C(X, Y)) :
    (mappingCylinderProjection f).comp (mappingCylinderTargetInclusion f) = ContinuousMap.id Y := by
  simpa [mappingCylinderProjection] using
    mappingCylinderDesc_comp_targetInclusion (ContinuousMap.id Y) (ContinuousMap.Homotopy.refl f)

/-- The canonical projection `M_f ⟶ Y` restricts on the cylinder side `X × I ⟶ M_f` to the map
`(x, t) ↦ f x`. -/
theorem mappingCylinderProjection_comp_cylinderInclusion (f : C(X, Y)) :
    (mappingCylinderProjection f).comp (mappingCylinderCylinderInclusion f) =
      f.comp ContinuousMap.fst := by
  rw [mappingCylinderProjection]
  rw [mappingCylinderDesc_comp_cylinderInclusion]
  ext x
  rfl

/-- Construction 6.3.1. Every map `f : X ⟶ Y` factors through its mapping cylinder
`M_f = Y ∪_f (X × I)` as `X ⟶ M_f ⟶ Y`. -/
theorem mappingCylinderFactorization (f : C(X, Y)) :
    (mappingCylinderProjection f).comp (mappingCylinderIn f) = f := by
  rw [mappingCylinderIn, ← ContinuousMap.comp_assoc,
    mappingCylinderProjection_comp_cylinderInclusion]
  ext x
  rfl

end
