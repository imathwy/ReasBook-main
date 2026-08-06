import Mathlib.CategoryTheory.CommSq
import Mathlib.Algebra.Exact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_2_1

open CategoryTheory
open HomotopicalAlgebra

noncomputable section

-- The local topological boundary-map owner is the Chapter 8 `cofiberStructureMap`, while the
-- cohomological suspension owner is the Chapter 19 accessor
-- `ReducedCohomologyTheory.suspensionIsoApp`. This file therefore uses a raw morphism
-- `cofiber i ⟶ ΣA` together with a Prop-valued specification exhibiting the chosen Chapter 19
-- cofiber and suspension models in a commutative comparison square with `cofiberStructureMap`,
-- and states Corollary 19.1.5 for the induced cohomology morphism.

local notation "NBasedSpace" => nondegeneratelyBasedSpace

/-- The cohomology morphism induced by a chosen boundary map `cofiber i ⟶ ΣA`, obtained by
composing the inverse of the canonical Chapter 19 suspension isomorphism
`(E (q + 1))(ΣA) ≅ (E ((q + 1) - 1))(A)`, after reindexing
`Ẽ^q(A) ≅ Ẽ^((q + 1) - 1)(A)`, with the contravariant map on `E^(q + 1)`. -/
noncomputable abbrev cofibrationBoundaryInducedCohomologyMap
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheory setup E]
    (q : ℤ) {A X : NBasedSpace} (i : A ⟶ X)
  (boundaryMap : setup.cofiber.obj (Arrow.mk i) ⟶ setup.suspension.obj A) :
    (E q).obj (Opposite.op A) ⟶
      (E (q + 1)).obj (Opposite.op (setup.cofiber.obj (Arrow.mk i))) :=
  (eqToIso (by
      have hq' : q + 1 - 1 = q := by
        rw [sub_eq_add_neg, add_assoc]
        simp
      have hq : q = q + 1 - 1 := hq'.symm
      exact congrArg (fun n ↦ (E n).obj (Opposite.op A)) hq)).hom ≫
    (ReducedCohomologyTheory.suspensionIsoApp (q + 1) A).symm.hom ≫
    (E (q + 1)).map boundaryMap.op

/-- The cofibration exactness axiom gives exactness at `Ẽ^q(X)` for the maps
`Ẽ^q(cofiber i) ⟶ Ẽ^q(X) ⟶ Ẽ^q(A)`. -/
theorem cofibrationBoundaryInducedCohomologyMap_exact_cofiberMap_i
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheory setup E]
    (q : ℤ) {A X : NBasedSpace} (i : A ⟶ X) [Cofibration i] :
    Function.Exact ((E q).map (setup.cofiberMap i).op) ((E q).map i.op) := by
  let hExact : ReducedCohomologyCofibrationExact setup E := inferInstance
  rcases hExact.exactness q i with ⟨δ, hδ⟩
  exact hδ.1

/-- A morphism `δ : Ẽ^q(A) ⟶ Ẽ^(q + 1)(cofiber i)` is a connecting morphism for the cofibration
`i` when it realizes the two source-facing exactness windows from Definition 19.2.1. -/
class IsCofibrationConnectingMorphism
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheory setup E]
    (q : ℤ) {A X : NBasedSpace} (i : A ⟶ X) [Cofibration i]
    (δ : (E q).obj (Opposite.op A) ⟶
      (E (q + 1)).obj (Opposite.op (setup.cofiber.obj (Arrow.mk i)))) : Prop where
  /-- The first exactness window is `Ẽ^q(cofiber i) ⟶ Ẽ^q(X) ⟶ Ẽ^q(A)`. -/
  exact₁ : Function.Exact ((E q).map (setup.cofiberMap i).op) ((E q).map i.op)
  /-- The second exactness window is `Ẽ^q(X) ⟶ Ẽ^q(A) ⟶ Ẽ^(q + 1)(cofiber i)`. -/
  exact₂ : Function.Exact ((E q).map i.op) δ

/-- A raw morphism `cofiber i ⟶ ΣA` is a topological boundary map for the cofibration `i` when
it comes equipped with comparison isomorphisms from the chosen Chapter 19 cofiber and suspension
models to the canonical Chapter 8 models under which it forms a commutative comparison square with
`cofiberStructureMap i`.
-/
class IsTopologicalCofibrationBoundaryMap
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    {A X : NBasedSpace} (i : A ⟶ X) [Cofibration i]
    (boundaryMap : setup.cofiber.obj (Arrow.mk i) ⟶ setup.suspension.obj A) : Prop where
  /-- Under suitable cofiber and suspension comparison isomorphisms, `boundaryMap` is the
  canonical topological boundary map `cofiberStructureMap i`, expressed by a commutative square. -/
  spec :
    ∃ (cofiberIso : (setup.cofiber.obj (Arrow.mk i)).obj ≅ homotopyCofiber i.hom)
      (suspensionIso : (setup.suspension.obj A).obj ≅ basedSuspension A.obj),
      CommSq boundaryMap.hom cofiberIso.hom suspensionIso.hom (cofiberStructureMap i.hom)

/-- A topological boundary map comes with comparison isomorphisms to the canonical Chapter 8
cofiber and suspension models, exhibiting a commutative comparison square. -/
theorem IsTopologicalCofibrationBoundaryMap.exists_comparison_isomorphisms
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    {A X : NBasedSpace} {i : A ⟶ X} [Cofibration i]
    {boundaryMap : setup.cofiber.obj (Arrow.mk i) ⟶ setup.suspension.obj A}
    (hboundary : IsTopologicalCofibrationBoundaryMap setup i boundaryMap) :
    ∃ (cofiberIso : (setup.cofiber.obj (Arrow.mk i)).obj ≅ homotopyCofiber i.hom)
      (suspensionIso : (setup.suspension.obj A).obj ≅ basedSuspension A.obj),
      CommSq boundaryMap.hom cofiberIso.hom suspensionIso.hom (cofiberStructureMap i.hom) :=
  hboundary.spec

/-- Corollary 19.1.5: the connecting homomorphism in the cohomology long exact sequence of a
cofibration is induced by the topological boundary map and the suspension isomorphism. If
`boundaryMap : cofiber i ⟶ ΣA` fits into the canonical comparison square with
`cofiberStructureMap i` under the chosen Chapter 19 cofiber and suspension models, then the
induced cohomology map
`cofibrationBoundaryInducedCohomologyMap setup E q i boundaryMap`
is a connecting morphism for the cofibration `i`, hence realizes the two exactness windows of
Definition 19.2.1. -/
theorem cofibrationBoundaryInducedCohomologyMap_isConnectingMorphism
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheory setup E]
    (q : ℤ) {A X : NBasedSpace} (i : A ⟶ X) [Cofibration i]
    (boundaryMap : setup.cofiber.obj (Arrow.mk i) ⟶ setup.suspension.obj A)
    (hboundary : IsTopologicalCofibrationBoundaryMap setup i boundaryMap) :
    IsCofibrationConnectingMorphism setup E q i
      (cofibrationBoundaryInducedCohomologyMap setup E q i boundaryMap) := by
  refine ⟨?_, ?_⟩
  · exact cofibrationBoundaryInducedCohomologyMap_exact_cofiberMap_i setup E q i
  · sorry

/-- The boundary-induced cohomology map is available to typeclass search as the connecting
morphism attached to the chosen topological boundary map. -/
instance cofibrationBoundaryInducedCohomologyMap_instIsCofibrationConnectingMorphism
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheory setup E]
    (q : ℤ) {A X : NBasedSpace} (i : A ⟶ X) [Cofibration i]
    (boundaryMap : setup.cofiber.obj (Arrow.mk i) ⟶ setup.suspension.obj A)
    (hboundary : IsTopologicalCofibrationBoundaryMap setup i boundaryMap) :
    IsCofibrationConnectingMorphism setup E q i
      (cofibrationBoundaryInducedCohomologyMap setup E q i boundaryMap) :=
  cofibrationBoundaryInducedCohomologyMap_isConnectingMorphism setup E q i boundaryMap hboundary

/-- If `boundaryMap` identifies with the canonical topological boundary map under the chosen
Chapter 19 models, then the induced cohomology map gives the second exactness window from
Definition 19.2.1. -/
theorem cofibrationBoundaryInducedCohomologyMap_exact_i
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheory setup E]
    (q : ℤ) {A X : NBasedSpace} (i : A ⟶ X) [Cofibration i]
    (boundaryMap : setup.cofiber.obj (Arrow.mk i) ⟶ setup.suspension.obj A)
    (hboundary : IsTopologicalCofibrationBoundaryMap setup i boundaryMap) :
    Function.Exact ((E q).map i.op)
      (cofibrationBoundaryInducedCohomologyMap setup E q i boundaryMap) :=
  (cofibrationBoundaryInducedCohomologyMap_isConnectingMorphism setup E q i boundaryMap
    hboundary).exact₂
