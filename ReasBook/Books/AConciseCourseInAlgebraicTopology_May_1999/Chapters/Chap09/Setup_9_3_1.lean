import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_6_1

open CategoryTheory Limits

noncomputable section

universe u

variable {E : Type u} {B : Type u} [TopologicalSpace E] [TopologicalSpace B]

/-- Setup 9.3.1: for a continuous map `p : C(E, B)`, and in particular for the fibrations with
path-connected base used in Chapter 9, a pointed fiber setup chooses a basepoint `base : B` and a
point `point` of the corresponding fiber `fiber p base = p ⁻¹' ({base} : Set B)`. The fibration
and path-connectedness hypotheses from the source setup are ambient assumptions, not part of this
chosen-data owner. -/
structure PointedFiberOfMap (p : C(E, B)) where
  /-- The chosen basepoint `* : B`. -/
  base : B
  /-- The chosen point of the fiber `fiber p base`. -/
  point : fiber p base

namespace PointedFiberOfMap

variable {p : C(E, B)}

/-- A pointed fiber setup canonically makes the chosen fiber inhabited. -/
instance instInhabitedFiber (s : PointedFiberOfMap p) : Inhabited (fiber p s.base) where
  default := s.point

/-- The chosen point of a pointed fiber setup projects to the chosen basepoint of `B`. -/
@[simp] theorem proj_point_eq_base (s : PointedFiberOfMap p) :
    p s.point = s.base := by
  exact Set.mem_singleton_iff.mp s.point.2

/-- The chosen fiber, regarded as a based space with basepoint `s.point`. -/
abbrev fiberSpace (s : PointedFiberOfMap p) : BasedSpace.{u} :=
  Under.mk <|
    show (⊤_ TopCat.{u}) ⟶ TopCat.of.{u} (fiber p s.base) from
      TopCat.terminalIsoPUnit.hom ≫ TopCat.ofHom (ContinuousMap.const PUnit s.point)

/-- The total space, pointed by the chosen fiber point. -/
abbrev totalSpace (s : PointedFiberOfMap p) : BasedSpace.{u} :=
  Under.mk <|
    show (⊤_ TopCat.{u}) ⟶ TopCat.of.{u} E from
      TopCat.terminalIsoPUnit.hom ≫ TopCat.ofHom (ContinuousMap.const PUnit s.point.1)

/-- The base space, pointed by the chosen basepoint `s.base`. -/
abbrev baseSpace (s : PointedFiberOfMap p) : BasedSpace.{u} :=
  Under.mk <|
    show (⊤_ TopCat.{u}) ⟶ TopCat.of.{u} B from
      TopCat.terminalIsoPUnit.hom ≫ TopCat.ofHom (ContinuousMap.const PUnit s.base)

/-- The underlying map `p` becomes a based map once the chosen point of the fiber is fixed. -/
theorem basedProjection_w (s : PointedFiberOfMap p) :
    (s.totalSpace).hom ≫
        (TopCat.ofHom p : TopCat.of.{u} E ⟶ TopCat.of.{u} B) =
      (s.baseSpace).hom := by
  ext u
  simp [proj_point_eq_base]

/-- The based map `p : s.totalSpace ⟶ s.baseSpace` determined by the chosen fiber point. -/
def basedProjection (s : PointedFiberOfMap p) : s.totalSpace ⟶ s.baseSpace :=
  Under.homMk
    (TopCat.ofHom p : TopCat.of.{u} E ⟶ TopCat.of.{u} B)
    (basedProjection_w s)

/-- The underlying map of `s.basedProjection` is `p`. -/
theorem basedProjection_hom (s : PointedFiberOfMap p) :
    (s.basedProjection).right.hom = p := rfl

/-- The inclusion of the chosen fiber into the chosen total space is a based map. -/
theorem fiberInclusionMap_w (s : PointedFiberOfMap p) :
    (s.fiberSpace).hom ≫
        (TopCat.ofHom (fiberInclusion p s.base) :
          TopCat.of.{u} (fiber p s.base) ⟶ TopCat.of.{u} E) =
      (s.totalSpace).hom := by
  ext u
  rfl

/-- The based inclusion of the chosen fiber into the total space. -/
def fiberInclusionMap (s : PointedFiberOfMap p) : s.fiberSpace ⟶ s.totalSpace :=
  Under.homMk
    (TopCat.ofHom (fiberInclusion p s.base) :
      TopCat.of.{u} (fiber p s.base) ⟶ TopCat.of.{u} E)
    (fiberInclusionMap_w s)

/-- The underlying map of `s.fiberInclusionMap` is the subtype inclusion of the fiber. -/
theorem fiberInclusionMap_hom (s : PointedFiberOfMap p) :
    (s.fiberInclusionMap).right.hom = fiberInclusion p s.base := rfl

end PointedFiberOfMap
