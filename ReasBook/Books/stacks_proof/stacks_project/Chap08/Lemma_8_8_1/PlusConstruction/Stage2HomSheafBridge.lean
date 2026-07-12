import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage2HomSheaf
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.StageInterfaces

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor
namespace LocallyDefinedHomTotal

private theorem sigma_mk_eq_mk_of_eq {α : Type u} {β : α → Type v}
    {a b : α} (h : a = b) (x : β a) :
    Sigma.mk b (Eq.mp (congrArg β h) x) = Sigma.mk a x := by
  cases h
  rfl

/-- Object-level core of source stage 2.8.

For the source locally-defined-Hom projection, a morphism inside the fiber over `U` is exactly a
plus-section with the fixed base arrow obtained from the two fiber-object base identifications.
This is the objectwise part of the eventual presheaf isomorphism used to prove that the stage-2
fiber Hom presheaves are sheaves. -/
noncomputable def sourceProjectionFiberHomFixedBaseEquiv
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C} :
    letI := sourceCategory (J := J) X
    ∀ (x y : (sourceProjection (J := J) X).Fiber U),
    (x ⟶ y) ≃
      ((J.over (X.p.obj x.1.obj)).plusObj
        (locallyDefinedHomSaturatedPresheaf X
          (eqToHom x.2 ≫ 𝟙 U ≫ eqToHom y.2.symm))).obj
        (op (Over.mk (𝟙 (X.p.obj x.1.obj)))) := by
  letI := sourceCategory (J := J) X
  intro x y
  let f₀ : X.p.obj x.1.obj ⟶ X.p.obj y.1.obj :=
    eqToHom x.2 ≫ 𝟙 U ≫ eqToHom y.2.symm
  let β : (X.p.obj x.1.obj ⟶ X.p.obj y.1.obj) → Type (max (max u v) vX) :=
    fun f => ((J.over (X.p.obj x.1.obj)).plusObj
      (locallyDefinedHomSaturatedPresheaf X f)).obj
        (op (Over.mk (𝟙 (X.p.obj x.1.obj))))
  refine
    { toFun := ?toFun
      invFun := ?invFun
      left_inv := ?left
      right_inv := ?right }
  · intro φ
    letI : (sourceProjection (J := J) X).IsHomLift (𝟙 U) φ.1 := φ.2
    have hbase : φ.1.1 = f₀ := by
      have hfac := IsHomLift.fac' (sourceProjection (J := J) X) (𝟙 U) φ.1
      simpa [sourceProjection, projectionMap, projectionObj, f₀, Category.assoc] using hfac
    exact Eq.mp (congrArg β hbase) φ.1.2
  · intro s
    refine ⟨⟨f₀, s⟩, ?_⟩
    refine IsHomLift.of_fac' (sourceProjection (J := J) X) (𝟙 U) ⟨f₀, s⟩ x.2 y.2 ?_
    simp [sourceProjection, projectionMap, projectionObj, f₀]
  · intro φ
    apply Subtype.ext
    letI : (sourceProjection (J := J) X).IsHomLift (𝟙 U) φ.1 := φ.2
    have hbase : φ.1.1 = f₀ := by
      have hfac := IsHomLift.fac' (sourceProjection (J := J) X) (𝟙 U) φ.1
      simpa [sourceProjection, projectionMap, projectionObj, f₀, Category.assoc] using hfac
    let ψ : locallyDefinedHom (J := J) X x.1.obj y.1.obj := φ.1
    change ψ.1 = f₀ at hbase
    change Sigma.mk f₀ (Eq.mp (congrArg β hbase) ψ.2) = ψ
    exact sigma_mk_eq_mk_of_eq (β := β) hbase ψ.2
  · intro s
    simp

/-- Source stage 2.8 bridge, isolated from the construction package.

The source proof says that the Hom presheaf of the pointwise locally-defined-Hom projection is
the plus construction on the separated Hom presheaf.  In Lean this is not a definitional
statement: the left side is the canonical fiber pseudofunctor of the stage-2 projection, while the
right side is a sheaf model built from explicit plus sections and owner transports.

This structure records exactly the missing bridge without pretending that the two owners are
definitionally equal. -/
structure PointwiseSourceHomSheafBridge
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- The source-text sheaf model for a stage-2 fiber Hom presheaf.  Concretely this should be
  the plus presheaf of locally-defined morphisms after all pullback-owner transports are
  expanded. -/
  sheafModel :
    ∀ (U : C)
      (_x _y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U),
      (Over U)ᵒᵖ ⥤ Type (max (max u v) vX)
  /-- The source-text model is a sheaf. -/
  sheafModel_isSheaf :
    ∀ (U : C)
      (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U),
      Presheaf.IsSheaf (J.over U) (sheafModel U x y)
  /-- Explicit comparison between the canonical fiber Hom presheaf and the source-text sheaf
  model.  This is the owner-sensitive part of stage 2.8. -/
  fiberHomIso :
    ∀ (U : C)
      (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U),
      ((canonicalFiberPseudofunctor
        (pointwiseSourceFibredCategory (J := J) X).p).presheafHom x y) ≅
        sheafModel U x y

namespace PointwiseSourceHomSheafBridge

/-- A completed stage-2 Hom-sheaf bridge supplies the exact Hom-sheaf obligation used by the
mixed-owner source stage-2 assembly. -/
theorem homSheaves
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (B : PointwiseSourceHomSheafBridge (J := J) X) :
    pointwiseSourceHomSheavesObligation (J := J) X := by
  intro U x y
  exact (Presheaf.isSheaf_of_iso_iff (B.fiberHomIso U x y)).2
    (B.sheafModel_isSheaf U x y)

/-- Build the mixed-owner stage-2 assembly once the source stage-2 Hom-sheaf bridge has been
proved. -/
noncomputable def toMixedAssembly
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (B : PointwiseSourceHomSheafBridge (J := J) X) :
    SourceHomSheafificationMixedAssembly (J := J) X :=
  pointwiseSourceHomSheafificationMixedAssembly (J := J) X B.homSheaves

end PointwiseSourceHomSheafBridge

/-- Source stage-2 bridge after the first local-equality quotient.  This is the stage required by
the plus-plus construction package. -/
abbrev SourceStage2HomSheafBridge
    (X : FibredCategoryOver.{u, v, uX, vX} C) :=
  PointwiseSourceHomSheafBridge (J := J) (separatedQuotientStage (J := J) X).quotient

/-- The post-quotient stage-2 bridge gives the exact field expected by
`SourceTextPlusPlusConstruction.stage2HomSheaves`. -/
theorem sourceStage2HomSheavesObligation_of_bridge
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (B : SourceStage2HomSheafBridge (J := J) X) :
    pointwiseSourceHomSheavesObligation
      (J := J) (separatedQuotientStage (J := J) X).quotient :=
  B.homSheaves

end LocallyDefinedHomTotal
end FibredCategoryMor

end CategoryTheory
