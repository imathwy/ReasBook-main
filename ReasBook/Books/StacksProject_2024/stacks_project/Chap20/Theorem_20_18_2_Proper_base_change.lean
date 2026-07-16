import StacksProject_2024.stacks_project.Chap05.Definition_5_17_2
import StacksProject_2024.stacks_project.Chap06.Lemma_6_21_6
import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_16
import StacksProject_2024.stacks_project.Chap13.Lemma_13_20_2
import StacksProject_2024.stacks_project.Chap20.Bounded_below_homotopy_category_comp_iso
import Mathlib.CategoryTheory.Whiskering

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open TopCat
open DerivedCategory.TStructure
open scoped TopCat

noncomputable section

universe u

namespace CategoryTheory.Sheaf

local notation "Ab(" X ")" => TopCat.Sheaf AddCommGrpCat X

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] mapBoundedBelowHomotopyToDerivedBelow_isLocalization

/-- Helper for Theorem 20.18.2 (Proper base change): the bounded-below homotopy-category lift of
an additive natural transformation is natural in the source complex. -/
private theorem mapBoundedBelowHomotopyNatTrans_naturality
    {𝒜 : Type u} {ℬ : Type u}
    [Category 𝒜] [Category ℬ] [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory ℬ]
    {F G : 𝒜 ⥤ ℬ} [F.Additive] [G.Additive] (τ : F ⟶ G)
    (K L : K⁺(𝒜)) (φ : K ⟶ L) :
    (CategoryTheory.mapBoundedBelowHomotopyCategory F).map φ ≫
      ObjectProperty.homMk ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app L.obj) =
        ObjectProperty.homMk
          ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K.obj) ≫
          (CategoryTheory.mapBoundedBelowHomotopyCategory G).map φ := by
  ext
  simpa using ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).naturality φ.hom)

/-- Helper for Theorem 20.18.2 (Proper base change): the bounded-below homotopy-category lift of
an additive natural transformation. -/
private noncomputable def mapBoundedBelowHomotopyNatTrans
    {𝒜 : Type u} {ℬ : Type u}
    [Category 𝒜] [Category ℬ] [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory ℬ]
    {F G : 𝒜 ⥤ ℬ} [F.Additive] [G.Additive] (τ : F ⟶ G) :
    CategoryTheory.mapBoundedBelowHomotopyCategory F ⟶
      CategoryTheory.mapBoundedBelowHomotopyCategory G :=
  NatTrans.mk
    (fun K ↦
      ObjectProperty.homMk ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K.obj))
    (mapBoundedBelowHomotopyNatTrans_naturality τ)

/-- Helper for Theorem 20.18.2 (Proper base change): the induced natural transformation on the
bounded-below homotopy-to-derived functors. -/
private noncomputable def mapBoundedBelowHomotopyToDerivedNatTrans
    {𝒜 : Type u} {ℬ : Type u}
    [Category 𝒜] [Category ℬ] [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory ℬ]
    {F G : 𝒜 ⥤ ℬ} [F.Additive] [G.Additive] (τ : F ⟶ G) :
    CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
      CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow G :=
  Functor.whiskerRight
    (mapBoundedBelowHomotopyNatTrans τ)
    (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow : K⁺(ℬ) ⥤ D⁺(ℬ))

/-- Helper for Theorem 20.18.2 (Proper base change): the bounded-below homotopy-to-derived functor
of a composite is canonically isomorphic to the iterated bounded-below functor. -/
private noncomputable def mapBoundedBelowHomotopyCategoryToDerivedBelowCompIso
    {𝒜 : Type u} {ℬ : Type u} {𝒞 : Type u}
    [Category 𝒜] [Category ℬ] [Category 𝒞]
    [Abelian 𝒜] [Abelian ℬ] [Abelian 𝒞] [HasDerivedCategory 𝒞]
    (F : 𝒜 ⥤ ℬ) (G : ℬ ⥤ 𝒞) [F.Additive] [G.Additive] :
    CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow (F ⋙ G) ≅
      CategoryTheory.mapBoundedBelowHomotopyCategory F ⋙
        CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow G :=
  Functor.isoWhiskerRight
    (CategoryTheory.mapBoundedBelowHomotopyCategoryCompIso F G)
    (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒞) ⥤ D⁺(𝒞)) ≪≫
      Functor.associator
        (CategoryTheory.mapBoundedBelowHomotopyCategory F)
        (CategoryTheory.mapBoundedBelowHomotopyCategory G)
        (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒞) ⥤ D⁺(𝒞))

section ProperBaseChange

variable {X Y Y' : TopCat.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)

local notation "AbX" => Ab(X)
local notation "AbY" => Ab(Y)
local notation "AbY'" => Ab(Y')
local notation "DAbX" => D⁺(AbX)
local notation "DAbY" => D⁺(AbY)
local notation "DAbY'" => D⁺(AbY')

/-- The pullback space `X' = Y' ×[Y] X` in the proper base change square. -/
abbrev properBaseChangePullback : TopCat.{u} := pullback f g

local notation "AbX'" => Ab(properBaseChangePullback f g)
local notation "DAbX'" => D⁺(AbX')
local notation "QX" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(AbX) ⥤ DAbX)
local notation "QY" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(AbY) ⥤ DAbY)
local notation "QX'" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(AbX') ⥤ DAbX')
local notation "QisX" => Qis⁺(AbX)
local notation "QisY" => Qis⁺(AbY)
local notation "QisX'" => Qis⁺(AbX')

/-- The projection `g' : X' ⟶ X` from the proper base change pullback. -/
abbrev properBaseChangeFst : properBaseChangePullback f g ⟶ X := pullback.fst f g

/-- The projection `f' : X' ⟶ Y'` from the proper base change pullback. -/
abbrev properBaseChangeSnd : properBaseChangePullback f g ⟶ Y' := pullback.snd f g

variable [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive]
variable [(TopCat.Sheaf.pullback AddCommGrpCat.{u} g).Additive]
variable [(TopCat.Sheaf.pullback AddCommGrpCat.{u} (properBaseChangeFst f g)).Additive]
variable [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} (properBaseChangeSnd f g)).Additive]

private noncomputable def boundedBelowHomotopyPushforward :
    K⁺(AbX) ⥤ K⁺(AbY) :=
  CategoryTheory.mapBoundedBelowHomotopyCategory
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)

private noncomputable def boundedBelowHomotopyPullbackFst :
    K⁺(AbX) ⥤ K⁺(AbX') :=
  CategoryTheory.mapBoundedBelowHomotopyCategory
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} (properBaseChangeFst f g))

private noncomputable def boundedBelowHomotopyPushforwardSnd :
    K⁺(AbX') ⥤ K⁺(AbY') :=
  CategoryTheory.mapBoundedBelowHomotopyCategory
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (properBaseChangeSnd f g))

private noncomputable def pushforwardToDerivedBelow :
    K⁺(AbX) ⥤ DAbY :=
  CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)

private noncomputable def pullbackToDerivedBelow :
    K⁺(AbY) ⥤ DAbY' :=
  CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} g)

private noncomputable def pullbackFstToDerivedBelow :
    K⁺(AbX) ⥤ DAbX' :=
  CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} (properBaseChangeFst f g))

private noncomputable def pushforwardSndToDerivedBelow :
    K⁺(AbX') ⥤ DAbY' :=
  CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (properBaseChangeSnd f g))

local notation "KfPush" =>
  ((boundedBelowHomotopyPushforward f) : K⁺(AbX) ⥤ K⁺(AbY))
local notation "KgPullFst" =>
  ((boundedBelowHomotopyPullbackFst f g) : K⁺(AbX) ⥤ K⁺(AbX'))
local notation "KfPushSnd" =>
  ((boundedBelowHomotopyPushforwardSnd f g) : K⁺(AbX') ⥤ K⁺(AbY'))
local notation "QfPush" =>
  ((pushforwardToDerivedBelow f) : K⁺(AbX) ⥤ DAbY)
local notation "QgPull" =>
  ((pullbackToDerivedBelow g) : K⁺(AbY) ⥤ DAbY')
local notation "QgPullFst" =>
  ((pullbackFstToDerivedBelow f g) : K⁺(AbX) ⥤ DAbX')
local notation "QfPushSnd" =>
  ((pushforwardSndToDerivedBelow f g) : K⁺(AbX') ⥤ DAbY')

private instance sheaf_enoughInjectives (T : TopCat.{u}) :
    EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{u} T) := by
  letI :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall
      (Opens.grothendieckTopology T) AddCommGrpCat.{u}
  exact
    (inferInstance :
      EnoughInjectives
        (CategoryTheory.Sheaf
          (Opens.grothendieckTopology T)
          AddCommGrpCat.{u}))

private instance pushforwardToDerivedBelow_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor QfPush QisX := by
  let _ : Functor.HasPointwiseRightDerivedFunctor QfPush QisX :=
    CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      QfPush
  infer_instance

private instance pullbackToDerivedBelow_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor QgPull QisY := by
  let _ : Functor.HasPointwiseRightDerivedFunctor QgPull QisY :=
    CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      QgPull
  infer_instance

private instance pullbackFstToDerivedBelow_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor QgPullFst QisX := by
  let _ : Functor.HasPointwiseRightDerivedFunctor QgPullFst QisX :=
    CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      QgPullFst
  infer_instance

private instance pushforwardSndToDerivedBelow_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor QfPushSnd QisX' := by
  let _ : Functor.HasPointwiseRightDerivedFunctor QfPushSnd QisX' :=
    CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      QfPushSnd
  infer_instance

private noncomputable def derivedPushforward :
    DAbX ⥤ DAbY :=
  let _ : Functor.HasRightDerivedFunctor QfPush QisX :=
    pushforwardToDerivedBelow_hasRightDerivedFunctor f
  Functor.totalRightDerived
    QfPush
    QX
    QisX

private noncomputable def derivedPullback :
    DAbY ⥤ DAbY' :=
  let _ : Functor.HasRightDerivedFunctor QgPull QisY :=
    pullbackToDerivedBelow_hasRightDerivedFunctor g
  Functor.totalRightDerived
    QgPull
    QY
    QisY

private noncomputable def derivedPullbackFst :
    DAbX ⥤ DAbX' :=
  let _ : Functor.HasRightDerivedFunctor QgPullFst QisX :=
    pullbackFstToDerivedBelow_hasRightDerivedFunctor f g
  Functor.totalRightDerived
    QgPullFst
    QX
    QisX

private noncomputable def derivedPushforwardSnd :
    DAbX' ⥤ DAbY' :=
  let _ : Functor.HasRightDerivedFunctor QfPushSnd QisX' :=
    pushforwardSndToDerivedBelow_hasRightDerivedFunctor f g
  Functor.totalRightDerived
    QfPushSnd
    QX'
    QisX'

local notation "Rf" => ((derivedPushforward f) : DAbX ⥤ DAbY)
local notation "Lg" => ((derivedPullback g) : DAbY ⥤ DAbY')
local notation "Lg'" => ((derivedPullbackFst f g) : DAbX ⥤ DAbX')
local notation "Rf'" => ((derivedPushforwardSnd f g) : DAbX' ⥤ DAbY')
local notation "PBSource" => Rf ⋙ Lg
local notation "PBTarget" => Lg' ⋙ Rf'

/-- The bounded-below derived source functor `g^{-1} ∘ Rf_*` in the proper base change square. -/
noncomputable def properBaseChangeSourceFunctor : D⁺(Ab(X)) ⥤ D⁺(Ab(Y')) :=
  PBSource

/-- The bounded-below derived target functor `Rf'_* ∘ (g')^{-1}` in the proper base change
square. -/
noncomputable def properBaseChangeTargetFunctor : D⁺(Ab(X)) ⥤ D⁺(Ab(Y')) :=
  PBTarget

/-- The source object `g^{-1} Rf_* E` of the proper base change comparison. -/
noncomputable def properBaseChangeSource (E : DAbX) : DAbY' :=
  (properBaseChangeSourceFunctor f g).obj E

/-- The target object `Rf'_* (g')^{-1} E` of the proper base change comparison. -/
noncomputable def properBaseChangeTarget (E : DAbX) : DAbY' :=
  (properBaseChangeTargetFunctor f g).obj E

omit [(TopCat.Sheaf.pullback AddCommGrpCat.{u} (properBaseChangeFst f g)).Additive]
  [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} (properBaseChangeSnd f g)).Additive] in
@[simp] theorem properBaseChangeSource_obj (E : DAbX) :
    ((properBaseChangeSourceFunctor f g) : DAbX ⥤ DAbY').obj E = properBaseChangeSource f g E :=
  rfl

omit [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive]
  [(TopCat.Sheaf.pullback AddCommGrpCat.{u} g).Additive] in
@[simp] theorem properBaseChangeTarget_obj (E : DAbX) :
    ((properBaseChangeTargetFunctor f g) : DAbX ⥤ DAbY').obj E = properBaseChangeTarget f g E :=
  rfl

local notation "f_*" => TopCat.Sheaf.pushforward AddCommGrpCat f
local notation "g^*" => TopCat.Sheaf.pullback AddCommGrpCat g
local notation "g'^*" => TopCat.Sheaf.pullback AddCommGrpCat (properBaseChangeFst f g)
local notation "f'_*" => TopCat.Sheaf.pushforward AddCommGrpCat (properBaseChangeSnd f g)

/-- The mixed bounded-below source comparison owner attached to `f_*` followed by bounded-below
derived pullback along `g`. -/
private def properBaseChangeSourceHomotopyFunctor :
    K⁺(AbX) ⥤ DAbY' :=
  KfPush ⋙ QgPull

private def properBaseChangeTargetHomotopyFunctor :
    K⁺(AbX) ⥤ DAbY' :=
  KgPullFst ⋙ QfPushSnd

local notation "PBSourceHomotopy" =>
  ((properBaseChangeSourceHomotopyFunctor f g) : K⁺(AbX) ⥤ DAbY')
local notation "PBTargetHomotopy" =>
  ((properBaseChangeTargetHomotopyFunctor f g) : K⁺(AbX) ⥤ DAbY')

/-- The mixed bounded-below source comparison owner attached to `f_*` followed by bounded-below
derived pullback along `g`. -/
private noncomputable def properBaseChangeCompositeSourceFunctor :
    DAbX ⥤ DAbY' :=
  Functor.totalRightDerived PBSourceHomotopy QX QisX

/-- The mixed bounded-below target comparison owner attached to pullback along `g'` followed by
bounded-below derived pushforward along `f'`. -/
private noncomputable def properBaseChangeCompositeTargetFunctor :
    DAbX ⥤ DAbY' :=
  Functor.totalRightDerived PBTargetHomotopy QX QisX

local notation "Rgf" =>
  ((properBaseChangeCompositeSourceFunctor f g) : DAbX ⥤ DAbY')
local notation "Rf'g'" =>
  ((properBaseChangeCompositeTargetFunctor f g) : DAbX ⥤ DAbY')

/-- The inverse-image square for abelian sheaves in the proper base-change pullback diagram.
This is the `AddCommGrpCat`-valued analogue of the set-sheaf bridge
`TopCat.Sheaf.properBaseChangeInverseImageSquare`, and it is the input square for the canonical
mate construction of the underived base-change morphism. -/
private noncomputable abbrev properBaseChangeAbelianInverseImageSquare :
    CategoryTheory.TwoSquare
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} g)
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} f)
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} (properBaseChangeSnd f g))
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} (properBaseChangeFst f g)) := by
  change
    TopCat.Sheaf.pullback AddCommGrpCat.{u} g ⋙
        TopCat.Sheaf.pullback AddCommGrpCat.{u} (properBaseChangeSnd f g) ⟶
      TopCat.Sheaf.pullback AddCommGrpCat.{u} f ⋙
        TopCat.Sheaf.pullback AddCommGrpCat.{u} (properBaseChangeFst f g)
  exact
    (TopCat.Sheaf.pullbackComp (properBaseChangeSnd f g) g).hom ≫
      eqToHom
        (congrArg
          (TopCat.Sheaf.pullback AddCommGrpCat.{u})
          (show properBaseChangeFst f g ≫ f = properBaseChangeSnd f g ≫ g from
            Limits.pullback.condition)).symm ≫
      (TopCat.Sheaf.pullbackComp (properBaseChangeFst f g) f).inv

/-- The underived proper-base-change natural transformation
`g^{-1} f_* ⟶ f'_* (g')^{-1}` on abelian sheaves. -/
private noncomputable def properBaseChangeUnderivedNatTrans :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
      TopCat.Sheaf.pullback AddCommGrpCat.{u} g) ⟶
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} (properBaseChangeFst f g) ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat.{u} (properBaseChangeSnd f g)) :=
  (CategoryTheory.mateEquiv
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (properBaseChangeSnd f g))
      (properBaseChangeAbelianInverseImageSquare f g)).natTrans

/-- Helper for Theorem 20.18.2 (Proper base change): the induced natural transformation on the
bounded-below homotopy-to-derived functors. -/
private noncomputable def properBaseChangeMapBoundedBelowHomotopyToDerivedNatTrans :
    CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) ⋙
          (TopCat.Sheaf.pullback AddCommGrpCat.{u} g)) ⟶
      CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (properBaseChangeFst f g)) ⋙
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (properBaseChangeSnd f g)) ) :=
  mapBoundedBelowHomotopyToDerivedNatTrans (properBaseChangeUnderivedNatTrans f g)
local notation "properBaseChangeMapBDerived" =>
  (properBaseChangeMapBoundedBelowHomotopyToDerivedNatTrans f g)

/-- Helper for Theorem 20.18.2 (Proper base change): the direct bounded-below comparison between
the mixed source and target functors. -/
private noncomputable def properBaseChangeDerivedComparisonNatTrans :
    KfPush ⋙ QgPull ⟶ KgPullFst ⋙ QfPushSnd :=
  (mapBoundedBelowHomotopyCategoryToDerivedBelowCompIso
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} g)).inv ≫
    properBaseChangeMapBDerived ≫
      (mapBoundedBelowHomotopyCategoryToDerivedBelowCompIso
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} (properBaseChangeFst f g))
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (properBaseChangeSnd f g))).hom
/-- The bounded-below right derived functor of `f_*` followed by bounded-below pullback along
`g` exists. -/
local instance properBaseChangePushforward_then_localization_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor
      (KfPush ⋙ QY)
      QisX := by
  let _ :
      Functor.HasPointwiseRightDerivedFunctor
        (KfPush ⋙ QY)
        QisX :=
    CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      (KfPush ⋙ QY)
  infer_instance

/-- The bounded-below right derived functor of pullback along `g'` followed by the canonical
bounded-below derived-category localization functor exists. -/
local instance properBaseChangePullbackFst_then_localization_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor
      (KgPullFst ⋙ QX')
      QisX := by
  let _ :
      Functor.HasPointwiseRightDerivedFunctor
        (KgPullFst ⋙ QX')
        QisX :=
    CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      (KgPullFst ⋙ QX')
  infer_instance

/-- The bounded-below right derived functor of `f_*` followed by bounded-below pullback along
`g` exists. -/
local instance properBaseChangeSourceHomotopyFunctor_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor PBSourceHomotopy QisX := by
  let _ :
      Functor.HasPointwiseRightDerivedFunctor PBSourceHomotopy QisX :=
    CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      PBSourceHomotopy
  infer_instance

/-- The bounded-below right derived functor of pullback along `g'` followed by bounded-below
pushforward along `f'` exists. -/
local instance properBaseChangeTargetHomotopyFunctor_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor PBTargetHomotopy QisX := by
  let _ :
      Functor.HasPointwiseRightDerivedFunctor PBTargetHomotopy QisX :=
    CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      PBTargetHomotopy
  infer_instance

private noncomputable def properBaseChangeCompositeSourceUnit :
    PBSourceHomotopy ⟶ QX ⋙ Rgf :=
  Functor.totalRightDerivedUnit PBSourceHomotopy QX QisX

private noncomputable def properBaseChangeCompositeTargetUnit :
    PBTargetHomotopy ⟶ QX ⋙ Rf'g' :=
  Functor.totalRightDerivedUnit PBTargetHomotopy QX QisX

private noncomputable def properBaseChangePushforwardUnit :
    KfPush ⋙ QY ⟶ QX ⋙ Rf :=
  Functor.totalRightDerivedUnit (KfPush ⋙ QY) QX QisX

private noncomputable def properBaseChangePullbackUnit :
    QgPull ⟶ QY ⋙ Lg :=
  Functor.totalRightDerivedUnit QgPull QY QisY

private noncomputable def properBaseChangePullbackFstUnit :
    KgPullFst ⋙ QX' ⟶ QX ⋙ Lg' :=
  Functor.totalRightDerivedUnit (KgPullFst ⋙ QX') QX QisX

private noncomputable def properBaseChangePushforwardSndUnit :
    QfPushSnd ⟶ QX' ⋙ Rf' :=
  Functor.totalRightDerivedUnit QfPushSnd QX' QisX'

local instance properBaseChangeCompositeSourceUnit_isRightDerivedFunctor :
    (properBaseChangeCompositeSourceFunctor f g).IsRightDerivedFunctor
      (properBaseChangeCompositeSourceUnit f g)
      QisX := by
  simpa [properBaseChangeCompositeSourceFunctor, properBaseChangeCompositeSourceUnit] using
    (inferInstance :
      (Functor.totalRightDerived PBSourceHomotopy QX QisX).IsRightDerivedFunctor
        (Functor.totalRightDerivedUnit PBSourceHomotopy QX QisX)
        QisX)

local instance properBaseChangeCompositeTargetUnit_isRightDerivedFunctor :
    (properBaseChangeCompositeTargetFunctor f g).IsRightDerivedFunctor
      (properBaseChangeCompositeTargetUnit f g)
      QisX := by
  simpa [properBaseChangeCompositeTargetFunctor, properBaseChangeCompositeTargetUnit] using
    (inferInstance :
      (Functor.totalRightDerived PBTargetHomotopy QX QisX).IsRightDerivedFunctor
        (Functor.totalRightDerivedUnit PBTargetHomotopy QX QisX)
        QisX)

private noncomputable def properBaseChangeCompositeDerivedData :
    PBSourceHomotopy ⟶ QX ⋙ Rf'g' :=
  properBaseChangeDerivedComparisonNatTrans f g ≫ properBaseChangeCompositeTargetUnit f g

private noncomputable def properBaseChangeCompositeDerivedNatTrans :
    Rgf ⟶ Rf'g' :=
  Functor.rightDerivedDesc
    Rgf
    (properBaseChangeCompositeSourceUnit f g)
    QisX
    Rf'g'
    (properBaseChangeCompositeDerivedData f g)

private noncomputable def sourceComparisonPullbackData :
    PBSourceHomotopy ⟶ KfPush ⋙ QY ⋙ Lg :=
  { app := fun E ↦
      (properBaseChangePullbackUnit g).app
        ((KfPush : K⁺(AbX) ⥤ K⁺(AbY)).obj E)
    naturality := by
      intro E₁ E₂ φ
      simpa using
        (properBaseChangePullbackUnit g).naturality
          ((KfPush : K⁺(AbX) ⥤ K⁺(AbY)).map φ) }

private noncomputable def sourceComparisonAssociatorHom :
    KfPush ⋙ QY ⋙ Lg ⟶ (KfPush ⋙ QY) ⋙ Lg :=
  { app := fun E ↦ 𝟙 _
    naturality := by
      intro E₁ E₂ φ
      simp }

private noncomputable def sourceComparisonPushforwardHom :
    (KfPush ⋙ QY) ⋙ Lg ⟶ (QX ⋙ Rf) ⋙ Lg :=
  { app := fun E ↦
      (Lg : DAbY ⥤ DAbY').map ((properBaseChangePushforwardUnit f).app E)
    naturality := by
      sorry }

private noncomputable def sourceComparisonPushforwardData :
    PBSourceHomotopy ⟶ (QX ⋙ Rf) ⋙ Lg :=
  sourceComparisonPullbackData f g ≫
    sourceComparisonAssociatorHom f g ≫
    sourceComparisonPushforwardHom f g

private noncomputable def sourceComparisonData :
    PBSourceHomotopy ⟶ QX ⋙ PBSource :=
  sourceComparisonPushforwardData f g ≫
    { app := fun E ↦ 𝟙 _
      naturality := by
        intro E₁ E₂ φ
        simp }

private noncomputable def sourceComparison :
    Rgf ⟶ PBSource :=
  Functor.rightDerivedDesc
    Rgf
    (properBaseChangeCompositeSourceUnit f g)
    QisX
    PBSource
    (sourceComparisonData f g)

private noncomputable def targetComparisonPushforwardData :
    PBTargetHomotopy ⟶ KgPullFst ⋙ QX' ⋙ Rf' :=
  { app := fun E ↦
      (properBaseChangePushforwardSndUnit f g).app
        ((KgPullFst : K⁺(AbX) ⥤ K⁺(AbX')).obj E)
    naturality := by
      intro E₁ E₂ φ
      simpa using
        (properBaseChangePushforwardSndUnit f g).naturality
          ((KgPullFst : K⁺(AbX) ⥤ K⁺(AbX')).map φ) }

private noncomputable def targetComparisonAssociatorData :
    PBTargetHomotopy ⟶ (KgPullFst ⋙ QX') ⋙ Rf' :=
  targetComparisonPushforwardData f g ≫
    { app := fun E ↦ 𝟙 _
      naturality := by
        intro E₁ E₂ φ
        simp }

private noncomputable def targetComparisonPullbackHom :
    (KgPullFst ⋙ QX') ⋙ Rf' ⟶ (QX ⋙ Lg') ⋙ Rf' :=
  { app := fun E ↦
      (Rf' : DAbX' ⥤ DAbY').map ((properBaseChangePullbackFstUnit f g).app E)
    naturality := by
      intro E₁ E₂ φ
      simpa only [Functor.map_comp] using
        congrArg (fun k ↦ (Rf' : DAbX' ⥤ DAbY').map k)
          ((properBaseChangePullbackFstUnit f g).naturality φ) }

private noncomputable def targetComparisonData :
    PBTargetHomotopy ⟶ QX ⋙ PBTarget :=
  targetComparisonAssociatorData f g ≫
    targetComparisonPullbackHom f g ≫
    { app := fun E ↦ 𝟙 _
      naturality := by
        intro E₁ E₂ φ
        simp }

private noncomputable def targetComparison :
    Rf'g' ⟶ PBTarget :=
  Functor.rightDerivedDesc
    Rf'g'
    (properBaseChangeCompositeTargetUnit f g)
    QisX
    PBTarget
    (targetComparisonData f g)

private noncomputable def properBaseChangeCompositeDerivedApp (E : DAbX) :
    ((properBaseChangeCompositeSourceFunctor f g) : DAbX ⥤ DAbY').obj E ⟶
      ((properBaseChangeCompositeTargetFunctor f g) : DAbX ⥤ DAbY').obj E :=
  (properBaseChangeCompositeDerivedNatTrans f g).app E

private noncomputable def sourceComparisonApp (E : DAbX) :
    ((properBaseChangeCompositeSourceFunctor f g) : DAbX ⥤ DAbY').obj E ⟶
      properBaseChangeSource f g E :=
  (sourceComparison f g).app E

private noncomputable def targetComparisonApp (E : DAbX) :
    ((properBaseChangeCompositeTargetFunctor f g) : DAbX ⥤ DAbY').obj E ⟶
      properBaseChangeTarget f g E :=
  (targetComparison f g).app E

/-- The canonical specification predicate for a bounded-below proper-base-change morphism:
it satisfies the canonical comparison identity induced by
`properBaseChangeUnderivedNatTrans`, via the source and target comparison morphisms. -/
def IsProperBaseChangeMap (E : DAbX)
    (η : properBaseChangeSource f g E ⟶ properBaseChangeTarget f g E) : Prop :=
  sourceComparisonApp f g E ≫ η =
    properBaseChangeCompositeDerivedApp f g E ≫ targetComparisonApp f g E

/-- The functor-level specification predicate for a bounded-below proper-base-change natural
transformation `g^{-1} ∘ Rf_* ⟶ Rf'_* ∘ (g')^{-1}`: each component satisfies the canonical
comparison identity induced by `properBaseChangeUnderivedNatTrans`. -/
def IsProperBaseChangeNatTrans
    (η : properBaseChangeSourceFunctor f g ⟶ properBaseChangeTargetFunctor f g) : Prop :=
  ∀ E : DAbX, IsProperBaseChangeMap f g E (η.app E)

/-- A bounded-below proper-base-change natural transformation satisfies the canonical comparison
identity after composing with the source and target comparison morphisms. -/
theorem IsProperBaseChangeNatTrans.comp_eq
    {η : properBaseChangeSourceFunctor f g ⟶ properBaseChangeTargetFunctor f g}
    (hη : IsProperBaseChangeNatTrans f g η) :
    sourceComparison f g ≫ η =
      properBaseChangeCompositeDerivedNatTrans f g ≫ targetComparison f g := by
  sorry

/-- A functor-level proper-base-change natural transformation induces componentwise bounded-below
proper-base-change morphisms. -/
theorem IsProperBaseChangeNatTrans.isProperBaseChangeMap_app
    {η : properBaseChangeSourceFunctor f g ⟶ properBaseChangeTargetFunctor f g}
    (hη : IsProperBaseChangeNatTrans f g η) (E : DAbX) :
    IsProperBaseChangeMap f g E (η.app E) := by
  exact hη E

/-- The functor-level proper-base-change predicate is equivalent to the componentwise proper-base-
change predicate on every bounded-below derived object. -/
theorem isProperBaseChangeNatTrans_iff
    {η : properBaseChangeSourceFunctor f g ⟶ properBaseChangeTargetFunctor f g} :
    IsProperBaseChangeNatTrans f g η ↔
      ∀ E : DAbX, IsProperBaseChangeMap f g E (η.app E) := by
  rfl

/-- Uniqueness for bounded-below proper-base-change morphisms satisfying the canonical
comparison identity. -/
theorem eq_of_isProperBaseChangeMap
    (E : D⁺(Ab(X)))
    {η₁ η₂ : properBaseChangeSource f g E ⟶ properBaseChangeTarget f g E}
    (hη₁ : IsProperBaseChangeMap f g E η₁)
    (hη₂ : IsProperBaseChangeMap f g E η₂) :
    η₁ = η₂ := by
  sorry

/-- Uniqueness for bounded-below proper-base-change natural transformations satisfying the
canonical comparison identity. -/
theorem eq_of_isProperBaseChangeNatTrans
    {η₁ η₂ : properBaseChangeSourceFunctor f g ⟶ properBaseChangeTargetFunctor f g}
    (hη₁ : IsProperBaseChangeNatTrans f g η₁)
    (hη₂ : IsProperBaseChangeNatTrans f g η₂) :
    η₁ = η₂ := by
  sorry

/-- Existence and uniqueness of the canonical bounded-below proper-base-change morphism whose
comparison identity is induced by `properBaseChangeUnderivedNatTrans`. -/
theorem existsUnique_properBaseChangeMap
    (E : D⁺(Ab(X))) :
    ∃! η : properBaseChangeSource f g E ⟶ properBaseChangeTarget f g E,
      IsProperBaseChangeMap f g E η := by
  sorry

end ProperBaseChange

section ProperBaseChangeTheorem

variable {X Y Y' : TopCat.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)

variable [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive]
variable [(TopCat.Sheaf.pullback AddCommGrpCat.{u} g).Additive]
variable [(TopCat.Sheaf.pullback AddCommGrpCat.{u} (properBaseChangeFst f g)).Additive]
variable [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} (properBaseChangeSnd f g)).Additive]
-- Proof sketch: reduce to stalks at points of `Y'`. Properness implies that `f` is closed and has
-- compact fibers, and the same remains true after base change. Apply the stalk/fiber comparison of
-- Lemma `20.18.1` to both sides, identify the fibers of `f` and `f'` over corresponding points by
-- the pullback square, and transport the restricted complex along that homeomorphism.
/-- Theorem 20.18.2 (Proper base change): under properness of `f`, any
bounded-below proper-base-change morphism satisfying the canonical comparison identity is an
isomorphism. Equivalently, the unique morphism characterized by
`IsProperBaseChangeMap f g E` is an isomorphism. -/
@[stacks 09V6]
theorem properBaseChange_isIso
    (hf : IsProperMap f) (E : D⁺(Ab(X)))
    {η : properBaseChangeSource f g E ⟶ properBaseChangeTarget f g E}
    (hη : IsProperBaseChangeMap f g E η) :
    IsIso η := by
  sorry

/-- Functor-level companion to Theorem 20.18.2: each component of a bounded-below proper-base-
change natural transformation is an isomorphism under properness of `f`. -/
theorem isIso_app_of_isProperBaseChangeNatTrans
    (hf : IsProperMap f) {η : properBaseChangeSourceFunctor f g ⟶ properBaseChangeTargetFunctor f g}
    (hη : IsProperBaseChangeNatTrans f g η) (E : D⁺(Ab(X))) :
    IsIso (η.app E) := by
  exact properBaseChange_isIso f g hf E (hη E)

/-- Automation-facing functor-level companion to Theorem 20.18.2: under properness of `f`, each
component of a bounded-below proper-base-change natural transformation is available to typeclass
search as an isomorphism. -/
instance instIsIsoAppOfIsProperBaseChangeNatTrans
    [hf : Fact (IsProperMap f)] {η : properBaseChangeSourceFunctor f g ⟶ properBaseChangeTargetFunctor f g}
    [hη : Fact (IsProperBaseChangeNatTrans f g η)] {E : D⁺(Ab(X))} :
    IsIso (η.app E) :=
  isIso_app_of_isProperBaseChangeNatTrans f g hf.out hη.out E

/-- Automation-facing companion to Theorem 20.18.2: under properness of `f`, any bounded-below
proper-base-change morphism satisfying the canonical comparison identity is available to
typeclass search as an isomorphism. -/
instance instIsIsoOfIsProperBaseChangeMap
    [hf : Fact (IsProperMap f)] {E : D⁺(Ab(X))}
    {η : properBaseChangeSource f g E ⟶ properBaseChangeTarget f g E}
    [hη : Fact (IsProperBaseChangeMap f g E η)] :
    IsIso η :=
  properBaseChange_isIso f g hf.out E hη.out

end ProperBaseChangeTheorem

end CategoryTheory.Sheaf
