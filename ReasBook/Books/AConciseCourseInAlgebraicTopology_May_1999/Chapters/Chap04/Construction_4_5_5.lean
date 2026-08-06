import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Construction_4_5_5.ConeAdjunction
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_8_10.ConnectedCovering

open TopCat

universe u

noncomputable section

section

variable {B : Type u} [TopologicalSpace B]

/-- Construction 4.5.5. For a chosen connected covering `X : ConnectedCoveringSpace B`,
with covering map `X.obj.hom : X.obj.left ⟶ B`, the space `B ∪_{X.obj.hom} CE` is the quotient
of `B ⊕ CE`, where `CE = (X.obj.left × I) / (X.obj.left × {1})`, obtained by identifying the
cone-base point `(e, 0)` with `X.obj.hom e`. -/
abbrev coveringConeAdjunctionSpace (X : ConnectedCoveringSpace B) : TopCat :=
  coneAdjunctionSpace (Hom.hom X.obj.hom)

/-- `coveringConeAdjunctionSpace X` is the adjunction space attached along the chosen covering
map `X.obj.hom`. -/
theorem coveringConeAdjunctionSpace_def (X : ConnectedCoveringSpace B) :
    coveringConeAdjunctionSpace X = coneAdjunctionSpace (Hom.hom X.obj.hom) :=
  rfl

namespace ConnectedCoveringSpace

/-- The `U` piece in Lemma 4.5.6 for the cone-adjunction space of the connected covering `X`. -/
abbrev coneAdjunctionSetU (X : ConnectedCoveringSpace B) :
    Set (coveringConeAdjunctionSpace X) :=
  _root_.coneAdjunctionSetU (Hom.hom X.obj.hom)

/-- The `V` piece in Lemma 4.5.6 for the cone-adjunction space of the connected covering `X`. -/
abbrev coneAdjunctionSetV (X : ConnectedCoveringSpace B) :
    Set (coveringConeAdjunctionSpace X) :=
  _root_.coneAdjunctionSetV (Hom.hom X.obj.hom)

/-- The overlap `U ∩ V` in Lemma 4.5.6 for the cone-adjunction space of the connected covering
`X`. -/
abbrev coneAdjunctionSetUInterV (X : ConnectedCoveringSpace B) :
    Set (coveringConeAdjunctionSpace X) :=
  _root_.coneAdjunctionSetUInterV (Hom.hom X.obj.hom)

/-- The canonical inclusion `B ⟶ U` in the covering-space context of Lemma 4.5.6. -/
abbrev coneAdjunctionSetUBaseMap (X : ConnectedCoveringSpace B) :
    C(B, X.coneAdjunctionSetU) :=
  _root_.coneAdjunctionSetUBaseMap (Hom.hom X.obj.hom)

/-- The canonical inclusion `X.obj.left ⟶ U ∩ V` in the covering-space context of Lemma 4.5.6. -/
abbrev coneAdjunctionSetUInterVMidpointMap (X : ConnectedCoveringSpace B) :
    C(X.obj.left, X.coneAdjunctionSetUInterV) :=
  _root_.coneAdjunctionSetUInterVMidpointMap (Hom.hom X.obj.hom)

end ConnectedCoveringSpace

end
