import StacksProject_2024.Chap15.Lemma_15_58_3
import StacksProject_2024.Chap21.Definition_21_17_13_Core

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open scoped RingedSiteDerivedTensor

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasColimits (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ M : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj M).Additive]
variable [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]
variable [∀ G₁ G₂ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ M : ringedSiteModuleCategory J 𝒪,
  PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J 𝒪))
    ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj M)]
variable [∀ M : ringedSiteModuleCategory J 𝒪,
  PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J 𝒪))
    ((curriedTensor (ringedSiteModuleCategory J 𝒪)).flip.obj M)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "Complexes" => CochainComplex Mod ℤ
local notation "KMod" => HomotopyCategory Mod (up ℤ)
local notation "DMod" => DerivedCategory Mod
local notation "Q" => (HomotopyCategory.quotient Mod (up ℤ) : Complexes ⥤ KMod)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso Mod (up ℤ)

local instance : MonoidalCategory KMod := inferInstance

local instance : (Q : Complexes ⥤ KMod).Monoidal := inferInstance

variable [MonoidalCategory (DerivedCategory (ringedSiteModuleCategory J 𝒪))]
variable [Functor.Monoidal
  (DerivedCategory.Qh :
    HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ) ⥤
      DerivedCategory (ringedSiteModuleCategory J 𝒪))]

/- Lemma 21.48.5 is a `bridge/view` item: the source-facing tensor object `K ⊗^L L` already lives
in `Definition_21_17_13_Core`, while this file records the canonical comparison morphism to the
ambient monoidal tensor on `D(𝒪_X)`. The comparison data stays axiom-clean by remaining
parametric in the ambient left-derived-functor witness. -/

private noncomputable abbrev tensorRightRepresentative
    (L : DMod) :
    KMod :=
  (Q : Complexes ⥤ KMod).obj ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L)

private noncomputable def tensorRightRepresentativeIso
    (L : DMod) :
    (((Qh : KMod ⥤ DMod)).obj (tensorRightRepresentative L)) ≅ L :=
  (DerivedCategory.quotientCompQhIso Mod).app
      ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L) ≪≫
    (DerivedCategory.Q : Complexes ⥤ DMod).objObjPreimageIso L

/-- Helper for Lemma 21.48.5: a monoidal functor commutes with tensoring on the right by a fixed
object. -/
private noncomputable def tensorRightCommIso
    {A : Type*} [Category A] [MonoidalCategory A]
    {B : Type*} [Category B] [MonoidalCategory B]
    (F : A ⥤ B) [Functor.Monoidal F] (X : A) :
    F ⋙ (tensoringRight B).obj (F.obj X) ≅ (tensoringRight A).obj X ⋙ F :=
  Functor.Monoidal.commTensorRight (F := F) X

/-- Helper for Lemma 21.48.5: on a represented homotopy-category morphism, the source tensor
functor is first computed in `KMod` by the raw quotient lift attached to a chosen representative
of `L`. -/
private noncomputable abbrev derivedTensorSourceLiftFunctor
    (L : DMod) :
    KMod ⥤ KMod :=
  let L' := (DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L
  CategoryTheory.Quotient.lift
      (homotopic Mod (up ℤ))
      ((((curriedTensor Mod).map₂CochainComplex).flip.obj L') ⋙ Q)
      (fun _ _ _ _ ⟨h⟩ ↦
        HomotopyCategory.eq_of_homotopy _ _
          (HomologicalComplex.mapBifunctorMapHomotopy₁ h
            (𝟙 L')
            (curriedTensor Mod)
            (up ℤ)))

/-- Helper for Lemma 21.48.5: on a represented homotopy-category morphism, the raw quotient-lift
source tensor functor map is computed by the chosen complex representative of `L`. -/
private theorem derivedTensorSourceLiftFunctor_map_quotientMap
    (L : DMod) {A B : Complexes} (f : A ⟶ B) :
    (derivedTensorSourceLiftFunctor L).map ((Q : Complexes ⥤ KMod).map f) =
      ((((curriedTensor Mod).map₂CochainComplex).flip.obj
        ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L)) ⋙ Q).map f := by
  let L' := (DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L
  -- Proof comment: this is the defining map formula for the quotient lift before composing with
  -- `Qh`, so the represented morphism is handled entirely in `KMod`.
  rfl

/-- Helper for Lemma 21.48.5: after fixing a representative of `L`, tensoring on the homotopy
category agrees with the raw quotient-lift source tensor functor in `KMod`. -/
private theorem tensoringRightRepresentativeIsoDerivedTensorSourceLiftFunctor_hom_naturality_repr
    (L : DMod) {A B : Complexes} (f : A ⟶ B) :
    ((tensoringRight KMod).obj (tensorRightRepresentative L)).map ((Q : Complexes ⥤ KMod).map f) ≫
        (Functor.Monoidal.μIso Q B
          ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L)).hom =
      (Functor.Monoidal.μIso Q A
        ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L)).hom ≫
          (derivedTensorSourceLiftFunctor L).map ((Q : Complexes ⥤ KMod).map f) := by
  let L' := (DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L
  -- Proof comment: rewrite the target map using the quotient-lift computation rule, then this is
  -- exactly the right-factor naturality of the monoidal structure map for `Q`.
  have hnat :
      ((tensoringRight KMod).obj (tensorRightRepresentative L)).map ((Q : Complexes ⥤ KMod).map f) ≫
          (Functor.Monoidal.μIso Q B L').hom =
        (Functor.Monoidal.μIso Q A L').hom ≫
          (Q : Complexes ⥤ KMod).map (f ▷ L') := by
    simpa [L', tensorRightRepresentative, tensorRightCommIso] using
      (tensorRightCommIso (F := Q) L').hom.naturality f
  have hsource :
      (Functor.Monoidal.μIso Q A L').hom ≫ (Q : Complexes ⥤ KMod).map (f ▷ L') =
        (Functor.Monoidal.μIso Q A L').hom ≫
          ((((curriedTensor Mod).map₂CochainComplex).flip.obj L') ⋙ Q).map f := by
    rfl
  have hmap :
      (Functor.Monoidal.μIso Q A L').hom ≫
          ((((curriedTensor Mod).map₂CochainComplex).flip.obj L') ⋙ Q).map f =
        (Functor.Monoidal.μIso Q A L').hom ≫
          (derivedTensorSourceLiftFunctor L).map ((Q : Complexes ⥤ KMod).map f) := by
    exact congrArg
      (fun k ↦ (Functor.Monoidal.μIso Q A L').hom ≫ k)
      (derivedTensorSourceLiftFunctor_map_quotientMap (L := L) f).symm
  exact hnat.trans (hsource.trans hmap)

/-- Helper for Lemma 21.48.5: after fixing a representative of `L`, tensoring on the homotopy
category agrees with the raw quotient-lift source tensor functor in `KMod`. -/
private noncomputable def tensoringRightRepresentativeIsoDerivedTensorSourceLiftFunctor
    (L : DMod) :
    (tensoringRight KMod).obj (tensorRightRepresentative L) ≅ derivedTensorSourceLiftFunctor L := by
  let L' := (DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L
  refine NatIso.ofComponents
    (fun A ↦ ?_)
    (fun {A B} f ↦ ?_)
  · -- Proof comment: on objects, the raw quotient lift is identified with right tensoring by the
    -- chosen representative through the monoidal tensorator of `Q`.
    simpa [L', derivedTensorSourceLiftFunctor, tensorRightRepresentative] using
      (Functor.Monoidal.μIso Q A.as L')
  · -- Proof comment: quotient induction reduces arbitrary `KMod` morphisms to represented chain
    -- maps, where the previous naturality lemma applies directly in `KMod`.
    rw [← HomotopyCategory.quotient_map_out (V := Mod) (c := up ℤ) f]
    simpa using
      tensoringRightRepresentativeIsoDerivedTensorSourceLiftFunctor_hom_naturality_repr
        (L := L) f.out

/-- Helper for Lemma 21.48.5: the raw quotient-side tensor bridge has the expected objectwise
component in `KMod`. -/
private theorem tensoringRightRepresentativeIsoDerivedTensorSourceLiftFunctor_hom_app
    (A : KMod) (L : DMod) :
    (tensoringRightRepresentativeIsoDerivedTensorSourceLiftFunctor L).hom.app A =
      (Functor.Monoidal.μIso Q A.as
        ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L)).hom := by
  -- Proof comment: this is the component specified in the `NatIso.ofComponents` definition.
  simp [tensoringRightRepresentativeIsoDerivedTensorSourceLiftFunctor]

/-- Helper for Lemma 21.48.5: after whiskering the `KMod` bridge by `Qh`, tensoring on the
homotopy category agrees with the source tensor functor before passing to the ambient tensor on
`D(𝒪)`. -/
private noncomputable def tensoringRightRepresentativeIsoDerivedTensorSourceFunctor
    (L : DMod) :
    (tensoringRight KMod).obj (tensorRightRepresentative L) ⋙ Qh ≅ derivedTensorSourceFunctor L := by
  -- Proof comment: the expensive DMod-valued bridge is now obtained by whiskering the cheaper
  -- `KMod`-valued comparison with `Qh`.
  simpa [derivedTensorSourceFunctor, derivedTensorSourceLiftFunctor] using
    (Functor.isoWhiskerRight
      (tensoringRightRepresentativeIsoDerivedTensorSourceLiftFunctor L)
      (Qh : KMod ⥤ DMod))

/-- Helper for Lemma 21.48.5: the quotient-side tensor bridge has the expected objectwise
component. -/
private theorem tensoringRightRepresentativeIsoDerivedTensorSourceFunctor_hom_app
    (A : KMod) (L : DMod) :
    (tensoringRightRepresentativeIsoDerivedTensorSourceFunctor L).hom.app A =
      ((Qh : KMod ⥤ DMod).mapIso
        (Functor.Monoidal.μIso Q A.as
          ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage L))).hom := by
  -- Proof comment: whiskering by `Qh` turns the `KMod` component into its image under `Qh.mapIso`.
  rfl

/-- Helper for Lemma 21.48.5: the ambient right-tensor functor on `D(𝒪)` agrees after whiskering
with `Qh` with the source tensor functor used to define `- ⊗^L L`. -/
private noncomputable def tensoringRightObjIsoDerivedTensorSourceFunctor
    (L : DMod) :
    Qh ⋙ (tensoringRight DMod).obj L ≅ derivedTensorSourceFunctor L :=
  -- Route correction: factor the bridge through the representative tensor object in `KMod`,
  -- commute `Qh` past right tensor once, and only then compare with the quotient-side source
  -- tensor functor.
  Functor.isoWhiskerLeft Qh (((tensoringRight DMod).mapIso (tensorRightRepresentativeIso L)).symm) ≪≫
    tensorRightCommIso Qh (tensorRightRepresentative L) ≪≫
      tensoringRightRepresentativeIsoDerivedTensorSourceFunctor L

/-- Helper for Lemma 21.48.5: the ambient right-tensor functor is already a left derived functor
of the source tensor functor because its whiskered comparison with `Qh` is an isomorphism. -/
private noncomputable instance tensoringRightObj_isLeftDerivedFunctor
    (L : DMod) :
    ((tensoringRight DMod).obj L).IsLeftDerivedFunctor
      (tensoringRightObjIsoDerivedTensorSourceFunctor L).hom
      Qis :=
  Functor.isLeftDerivedFunctor_of_inverts
    Qis
    ((tensoringRight DMod).obj L)
    (tensoringRightObjIsoDerivedTensorSourceFunctor L)

/-- Helper for Lemma 21.48.5: the ambient right-tensor functor on `D(𝒪)` is canonically
identified with the source-facing derived tensor functor `derivedTensorProduct L`. -/
private noncomputable def tensoringRightObjIsoDerivedTensorProduct
    (L : DMod) :
    (tensoringRight DMod).obj L ≅ derivedTensorProduct L :=
  let F : KMod ⥤ DMod := derivedTensorSourceFunctor L
  -- Proof comment: both functors are left derived functors of the same source functor `F`, so
  -- uniqueness of left derived functors gives the comparison isomorphism directly.
  (show (tensoringRight DMod).obj L ≅ derivedTensorProduct L from
    Functor.leftDerivedNatIso
      ((tensoringRight DMod).obj L)
      (derivedTensorProduct L)
      (tensoringRightObjIsoDerivedTensorSourceFunctor L).hom
      (derivedTensorProductCounit L)
      Qis
      (Iso.refl F))

/-- The canonical comparison morphism from the source-facing derived tensor product `K ⊗^L L` to
the ambient monoidal tensor object `K ⊗ L` on `D(𝒪_X)`. The data remain parametric in the
left-derived-functor witness for `derivedTensorSourceFunctor L`, so this declaration does not bake
the proof-heavy instance from `Definition_21_17_13_Core` into new concrete data. -/
noncomputable def derivedTensorProductToTensorComparison
    (K L : DMod)
    [(derivedTensorSourceFunctor L).HasLeftDerivedFunctor Qis] :
    K ⊗^L L ⟶ K ⊗ L :=
  -- Proof comment: the ambient right-tensor functor is canonically isomorphic to derived tensoring
  -- with `L`, so the desired comparison is the inverse component of that functor isomorphism.
  (tensoringRightObjIsoDerivedTensorProduct L).inv.app K

/-- Lemma 21.48.5: the canonical comparison morphism
`derivedTensorProductToTensorComparison K L : K ⊗^L L ⟶ K ⊗ L`, obtained from the derived-tensor
counit and the ambient monoidal structure on `D(𝒪_X)`, is an isomorphism. -/
@[stacks 0FPT, instance]
theorem isIso_derivedTensorProductToTensorComparison
    (K L : DMod) :
    IsIso (derivedTensorProductToTensorComparison K L) := by
  -- Proof comment: this is the component of the inverse of a functor isomorphism.
  simpa [derivedTensorProductToTensorComparison] using
    (inferInstance : IsIso ((tensoringRightObjIsoDerivedTensorProduct L).inv.app K))

end

end SheafOfModules.RingedSite
