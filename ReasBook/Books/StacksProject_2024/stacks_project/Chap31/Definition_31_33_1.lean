import Mathlib
import StacksProject_2024.stacks_project.Chap06.ClosedSubsetInclusion
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Opposite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall note: `lean_leansearch` pointed to the `Scheme.IdealSheafData` API, and the
-- local closed-support construction was checked against the Chapter 17 owner pattern before being
-- specialized here to the single subsheaf needed for strict transforms.

section

variable {S S' X : Scheme.{u}}
variable (b : S' ⟶ S)

/-- The pullback scheme underlying the strict-transform construction. -/
abbrev strictTransformAmbient (f : X ⟶ S) : Scheme.{u} :=
  pullback f b

/-- The pullback support of the exceptional divisor on the ambient pullback scheme. -/
abbrev strictTransformPullbackSupport
    (E : S'.IdealSheafData) (f : X ⟶ S) :
    Set (strictTransformAmbient b f) :=
  (((E.comap (pullback.snd f b)).support :
      TopologicalSpace.Closeds (strictTransformAmbient b f)) :
    Set (strictTransformAmbient b f))

private abbrev strictTransformPullbackSupportIsClosed
    (E : S'.IdealSheafData) (f : X ⟶ S) :
    IsClosed (strictTransformPullbackSupport b E f) :=
  (E.comap (pullback.snd f b)).support.2

/-- The structure sheaf on the pullback scheme used in the strict-transform construction. -/
private abbrev strictTransformRingSheaf (f : X ⟶ S) :
    TopCat.Sheaf RingCat.{u} (strictTransformAmbient b f) :=
  (strictTransformAmbient b f).ringCatSheaf

private theorem strictTransformUnitObj_eq_ringObj
    (f : X ⟶ S) (U : Opens (strictTransformAmbient b f)) :
    (((SheafOfModules.unit (strictTransformRingSheaf b f)).val.obj (op U) : Type u)) =
      (strictTransformAmbient b f).presheaf.obj (op U) := by
  rfl

private abbrev strictTransformUnitSectionToRingSection
    (f : X ⟶ S) (U : Opens (strictTransformAmbient b f)) :
    (SheafOfModules.unit (strictTransformRingSheaf b f)).val.obj (op U) →
      (strictTransformAmbient b f).presheaf.obj (op U) :=
  Eq.mp (strictTransformUnitObj_eq_ringObj (b := b) f U)

/-- The category of module sheaves on the pullback scheme used in the strict-transform
construction. -/
private abbrev strictTransformModuleCat (f : X ⟶ S) :=
  (strictTransformAmbient b f).Modules

/-- The open complement of the exceptional pullback support in the ambient pullback scheme. -/
private abbrev strictTransformOpenComplement
    (E : S'.IdealSheafData) (f : X ⟶ S) :
    Opens (strictTransformAmbient b f) :=
  ⟨(strictTransformPullbackSupport b E f)ᶜ,
    (strictTransformPullbackSupportIsClosed b E f).isOpen_compl⟩

/-- The structure-sheaf map attached to restricting from the ambient pullback scheme to the open
complement of the exceptional pullback support. -/
private abbrev strictTransformOpenComplementStructureSheafHom
    (E : S'.IdealSheafData) (f : X ⟶ S) :
    strictTransformRingSheaf b f ⟶
      (TopCat.Sheaf.pushforward RingCat.{u}
        (strictTransformOpenComplement b E f).inclusion').obj
          ((TopCat.Sheaf.pullback RingCat.{u}
            (strictTransformOpenComplement b E f).inclusion').obj
              (strictTransformRingSheaf b f)) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
    (strictTransformOpenComplement b E f).inclusion').unit.app
      (strictTransformRingSheaf b f)

/-- Restriction of modules on the ambient pullback scheme to the open complement of the pullback
support. -/
private abbrev strictTransformOpenComplementRestrictionFunctor
    (E : S'.IdealSheafData) (f : X ⟶ S) :
    strictTransformModuleCat b f ⥤
      SheafOfModules
        ((TopCat.Sheaf.pullback RingCat.{u}
          (strictTransformOpenComplement b E f).inclusion').obj
            (strictTransformRingSheaf b f)) :=
  moduleSheafRestrictionToOpen
    (strictTransformOpenComplement b E f) (strictTransformRingSheaf b f)

private instance strictTransformOpenComplementPushforward_isRightAdjoint
    (E : S'.IdealSheafData) (f : X ⟶ S) :
    (SheafOfModules.pushforward.{u}
      (strictTransformOpenComplementStructureSheafHom b E f)).IsRightAdjoint :=
  SheafOfModules.instIsRightAdjointPushforward
    (φ := strictTransformOpenComplementStructureSheafHom b E f)

/-- The canonical restriction map to the open complement of the pullback support. -/
private abbrev strictTransformOpenComplementRestriction
    (E : S'.IdealSheafData) (f : X ⟶ S) (ℱ : strictTransformModuleCat b f) :
    ℱ ⟶
      (SheafOfModules.pushforward
        (strictTransformOpenComplementStructureSheafHom b E f)).obj
          ((strictTransformOpenComplementRestrictionFunctor b E f).obj ℱ) :=
  (SheafOfModules.pullbackPushforwardAdjunction
    (strictTransformOpenComplementStructureSheafHom b E f)).unit.app ℱ

/-- Pullback of `\mathcal O_X`-modules to the ambient pullback scheme of the strict transform. -/
abbrev strictTransformPullbackFunctor (f : X ⟶ S) :
    X.Modules ⥤ strictTransformModuleCat b f :=
  RingedSpace.Hom.pullback (pullback.fst f b).toShHom

/-- The submodule of sections whose support lies in the inverse image of the exceptional divisor
on the ambient pullback scheme. -/
abbrev strictTransformSupportedSubsheaf
    (E : S'.IdealSheafData) (f : X ⟶ S) (ℱ : strictTransformModuleCat b f) :
    Subobject ℱ :=
  kernelSubobject (strictTransformOpenComplementRestriction b E f ℱ)

/-- The strict-transform support subsheaf is the canonical closed-support kernel on the ambient
pullback scheme. -/
theorem strictTransformSupportedSubsheaf_eq_kernel
    (E : S'.IdealSheafData) (f : X ⟶ S) (ℱ : strictTransformModuleCat b f) :
    strictTransformSupportedSubsheaf b E f ℱ =
      kernelSubobject
        (strictTransformOpenComplementRestriction b E f ℱ) :=
  rfl

private theorem strictTransformSupportedSubsheafMap_w
    (E : S'.IdealSheafData) (f : X ⟶ S)
    {ℱ 𝒢 : strictTransformModuleCat b f} (φ : ℱ ⟶ 𝒢) :
    φ ≫ strictTransformOpenComplementRestriction b E f 𝒢 =
      strictTransformOpenComplementRestriction b E f ℱ ≫
        (SheafOfModules.pushforward
          (strictTransformOpenComplementStructureSheafHom b E f)).map
            ((strictTransformOpenComplementRestrictionFunctor b E f).map φ) := by
  simpa using
    (SheafOfModules.pullbackPushforwardAdjunction
      (strictTransformOpenComplementStructureSheafHom b E f)).unit.naturality φ

private def strictTransformSupportedSubsheafMap
    (E : S'.IdealSheafData) (f : X ⟶ S)
    {ℱ 𝒢 : strictTransformModuleCat b f} (φ : ℱ ⟶ 𝒢) :
    ((strictTransformSupportedSubsheaf b E f ℱ : Subobject ℱ) : strictTransformModuleCat b f) ⟶
      ((strictTransformSupportedSubsheaf b E f 𝒢 : Subobject 𝒢) : strictTransformModuleCat b f) :=
  kernelSubobjectMap <|
    Arrow.homMk'
      φ
      ((SheafOfModules.pushforward
        (strictTransformOpenComplementStructureSheafHom b E f)).map
          ((strictTransformOpenComplementRestrictionFunctor b E f).map φ))
      (strictTransformSupportedSubsheafMap_w b E f φ)

/-- The ideal of sections of `\mathcal O_Y` generated by a subobject of the structure sheaf over
an open subset `U ⊆ Y`. -/
private noncomputable def idealSectionIdeal
    (f : X ⟶ S)
    (I : Subobject
      (SheafOfModules.unit (strictTransformRingSheaf b f) :
        strictTransformModuleCat b f))
    (U : (Opens (strictTransformAmbient b f))ᵒᵖ) :
  Ideal ((strictTransformAmbient b f).presheaf.obj U) :=
  let iArrow := I.arrow.val
  Ideal.span <| Set.range fun s :
      (Subobject.underlying.obj I).val.obj U ↦
    strictTransformUnitSectionToRingSection b f (Opposite.unop U) ((iArrow.app U) s)

/-- Definition 31.33.1 (1): for a morphism `f : X ⟶ S`, a morphism `b : S' ⟶ S`, and an
exceptional divisor `E` on `S'`, the strict transform of an `\mathcal O_X`-module `\mathcal F`
is the quotient of `\mathrm{pr}_X^* \mathcal F` by the submodule of sections supported on
`\mathrm{pr}_{S'}^{-1}E`. -/
@[stacks 080D]
noncomputable def strictTransformModule
    (E : S'.IdealSheafData) (f : X ⟶ S) (ℱ : X.Modules) :
    (strictTransformAmbient b f).Modules :=
  cokernel <| (strictTransformSupportedSubsheaf b E f
    ((strictTransformPullbackFunctor b f).obj ℱ)).arrow

/-- The module strict transform is functorial in the source module. -/
noncomputable def strictTransformFunctor
    (E : S'.IdealSheafData) (f : X ⟶ S) :
    X.Modules ⥤ (strictTransformAmbient b f).Modules where
  obj ℱ := strictTransformModule b E f ℱ
  map φ :=
    cokernel.map
      (strictTransformSupportedSubsheaf b E f
        ((strictTransformPullbackFunctor b f).obj _)).arrow
      (strictTransformSupportedSubsheaf b E f
        ((strictTransformPullbackFunctor b f).obj _)).arrow
      (strictTransformSupportedSubsheafMap b E f
        ((strictTransformPullbackFunctor b f).map φ))
      ((strictTransformPullbackFunctor b f).map φ)
      (by
        simpa [strictTransformSupportedSubsheafMap] using
          Limits.kernelSubobjectMap_arrow <|
            strictTransformSupportedSubsheafMap b E f
              ((strictTransformPullbackFunctor b f).map φ))
  map_id := by
    intro ℱ
    apply (cancel_epi
      (cokernel.π <|
        (strictTransformSupportedSubsheaf b E f
          ((strictTransformPullbackFunctor b f).obj ℱ)).arrow)).1
    simp [strictTransformPullbackFunctor, strictTransformModule]
  map_comp := by
    intro ℱ 𝒢 ℋ φ ψ
    apply (cancel_epi
      (cokernel.π <|
        (strictTransformSupportedSubsheaf b E f
          ((strictTransformPullbackFunctor b f).obj ℱ)).arrow)).1
    simp [strictTransformPullbackFunctor, strictTransformModule]

/-- The ideal sheaf data cutting out the strict transform as a closed subscheme of the ambient
pullback scheme. -/
noncomputable def strictTransformIdealSheafData
    (E : S'.IdealSheafData) (f : X ⟶ S) :
    (strictTransformAmbient b f).IdealSheafData :=
  let I : Subobject
      (SheafOfModules.unit (strictTransformRingSheaf b f) :
        strictTransformModuleCat b f) :=
    strictTransformSupportedSubsheaf b E f
      (SheafOfModules.unit (strictTransformRingSheaf b f) :
        strictTransformModuleCat b f)
  Scheme.IdealSheafData.ofIdeals fun U : (strictTransformAmbient b f).affineOpens ↦
    idealSectionIdeal b f I (Opposite.op U.1)

/-- Definition 31.33.1 (2): the strict transform of `X` is the closed subscheme of
`X \times_S S'` cut out by the ideal of sections of `\mathcal O_{X \times_S S'}` supported on
`\mathrm{pr}_{S'}^{-1}E`. -/
@[stacks 080D]
noncomputable def strictTransform (E : S'.IdealSheafData) (f : X ⟶ S) : Scheme :=
  (strictTransformIdealSheafData b E f).subscheme

end

end AlgebraicGeometry
