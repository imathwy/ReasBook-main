import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.UnitInterval
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_2_1

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

noncomputable section

universe u

variable {A B C : Type u} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

-- Semantic recall via `lean_leansearch`: no verified dedicated topological-space owner for the
-- double mapping cylinder surfaced in the current environment. The existing Chapter 6 mapping
-- cylinder files model this kind of gluing in `TopCat` by a pushout, so we present `M(i, j)` as
-- the pushout of the boundary map `C ⊕ C ⟶ C × I` and the attaching map `C ⊕ C ⟶ A ⊕ B`.

namespace ContinuousMap

/-- The right endpoint inclusion `C ⟶ C × I` used in the double mapping cylinder. -/
def doubleMappingCylinderTimeOneInclusion (X : Type u) [TopologicalSpace X] : C(X, X × I) :=
  (ContinuousMap.id X).prodMk (ContinuousMap.const X (1 : I))

@[simp] theorem doubleMappingCylinderTimeOneInclusion_apply
    (X : Type u) [TopologicalSpace X] (x : X) :
    doubleMappingCylinderTimeOneInclusion X x = (x, (1 : I)) :=
  rfl

/-- The boundary map `C ⊕ C ⟶ C × I` sending the left copy of `C` to `C × {0}` and the right copy
of `C` to `C × {1}`. -/
def doubleMappingCylinderBoundaryMap (X : Type u) [TopologicalSpace X] : C(X ⊕ X, X × I) :=
  { toFun :=
      Sum.elim (mappingCylinderTimeZeroInclusion X) (doubleMappingCylinderTimeOneInclusion X)
    continuous_toFun :=
      Continuous.sumElim
        (mappingCylinderTimeZeroInclusion X).continuous
        (doubleMappingCylinderTimeOneInclusion X).continuous }

@[simp] theorem doubleMappingCylinderBoundaryMap_inl
    (X : Type u) [TopologicalSpace X] (x : X) :
    doubleMappingCylinderBoundaryMap X (Sum.inl x) = (x, (0 : I)) :=
  rfl

@[simp] theorem doubleMappingCylinderBoundaryMap_inr
    (X : Type u) [TopologicalSpace X] (x : X) :
    doubleMappingCylinderBoundaryMap X (Sum.inr x) = (x, (1 : I)) :=
  rfl

/-- The attaching map `C ⊕ C ⟶ A ⊕ B` induced by `i : C(C, A)` on the left summand and
`j : C(C, B)` on the right summand. -/
def doubleMappingCylinderAttachMap (i : C(C, A)) (j : C(C, B)) : C(C ⊕ C, A ⊕ B) :=
  { toFun := Sum.elim (fun c ↦ Sum.inl (i c)) (fun c ↦ Sum.inr (j c))
    continuous_toFun :=
      Continuous.sumElim
        (continuous_inl.comp i.continuous)
        (continuous_inr.comp j.continuous) }

@[simp] theorem doubleMappingCylinderAttachMap_inl
    (i : C(C, A)) (j : C(C, B)) (c : C) :
    doubleMappingCylinderAttachMap i j (Sum.inl c) = Sum.inl (i c) :=
  rfl

@[simp] theorem doubleMappingCylinderAttachMap_inr
    (i : C(C, A)) (j : C(C, B)) (c : C) :
    doubleMappingCylinderAttachMap i j (Sum.inr c) = Sum.inr (j c) :=
  rfl

/-- Definition 10.7.6. For maps `i : C(C, A)` and `j : C(C, B)`, the double mapping cylinder
`M(i, j)` is the pushout of the attaching map `C ⊕ C ⟶ A ⊕ B` and the boundary map
`C ⊕ C ⟶ C × I`, i.e. the space `A ∪ (C × I) ∪ B` obtained by gluing `C × {0}` to `A` and
`C × {1}` to `B`. -/
abbrev doubleMappingCylinder (i : C(C, A)) (j : C(C, B)) : TopCat :=
  pushout (TopCat.ofHom (doubleMappingCylinderAttachMap i j))
    (TopCat.ofHom (doubleMappingCylinderBoundaryMap C))

scoped notation "M(" i ", " j ")" => doubleMappingCylinder i j

open scoped ContinuousMap

/-- The canonical inclusion `A ⊕ B ⟶ M(i, j)` of the two end summands into the double mapping
cylinder. -/
def doubleMappingCylinderCoprodInclusion (i : C(C, A)) (j : C(C, B)) :
    C(A ⊕ B, M(i, j)) :=
  (pushout.inl (TopCat.ofHom (doubleMappingCylinderAttachMap i j))
    (TopCat.ofHom (doubleMappingCylinderBoundaryMap C))).hom

/-- The canonical inclusion `C × I ⟶ M(i, j)` of the cylinder side into the double mapping
cylinder. -/
def doubleMappingCylinderCylinderInclusion (i : C(C, A)) (j : C(C, B)) :
    C(C × I, M(i, j)) :=
  (pushout.inr (TopCat.ofHom (doubleMappingCylinderAttachMap i j))
    (TopCat.ofHom (doubleMappingCylinderBoundaryMap C))).hom

/-- The canonical inclusions into `M(i, j)` form a commuting square with the attaching map
`C ⊕ C ⟶ A ⊕ B` and the boundary map `C ⊕ C ⟶ C × I`. -/
theorem doubleMappingCylinderInclusion_commSq (i : C(C, A)) (j : C(C, B)) :
    CommSq (TopCat.ofHom (doubleMappingCylinderAttachMap i j))
      (TopCat.ofHom (doubleMappingCylinderBoundaryMap C))
      (TopCat.ofHom (doubleMappingCylinderCoprodInclusion i j))
      (TopCat.ofHom (doubleMappingCylinderCylinderInclusion i j)) := by
  refine ⟨?_⟩
  simpa [doubleMappingCylinderCoprodInclusion, doubleMappingCylinderCylinderInclusion] using
    (pushout.condition :
      TopCat.ofHom (doubleMappingCylinderAttachMap i j) ≫
          pushout.inl (TopCat.ofHom (doubleMappingCylinderAttachMap i j))
            (TopCat.ofHom (doubleMappingCylinderBoundaryMap C)) =
        TopCat.ofHom (doubleMappingCylinderBoundaryMap C) ≫
          pushout.inr (TopCat.ofHom (doubleMappingCylinderAttachMap i j))
            (TopCat.ofHom (doubleMappingCylinderBoundaryMap C)))

/-- The canonical inclusions into `M(i, j)` agree on `C ⊕ C` along the attaching and boundary
maps. -/
theorem doubleMappingCylinderCoprodInclusion_comp (i : C(C, A)) (j : C(C, B)) :
    (doubleMappingCylinderCoprodInclusion i j).comp (doubleMappingCylinderAttachMap i j) =
      (doubleMappingCylinderCylinderInclusion i j).comp (doubleMappingCylinderBoundaryMap C) := by
  simpa using congrArg TopCat.Hom.hom (doubleMappingCylinderInclusion_commSq i j).w

/-- Unfolding `doubleMappingCylinder` identifies it with the pushout of the attaching and boundary
maps used to glue `A`, `C × I`, and `B`. -/
theorem doubleMappingCylinder_def (i : C(C, A)) (j : C(C, B)) :
    M(i, j) =
      pushout (TopCat.ofHom (doubleMappingCylinderAttachMap i j))
        (TopCat.ofHom (doubleMappingCylinderBoundaryMap C)) :=
  rfl

end ContinuousMap
