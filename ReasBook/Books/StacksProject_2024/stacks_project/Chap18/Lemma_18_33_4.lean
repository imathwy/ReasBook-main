import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_28_1
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategoryBasic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction
open scoped RelativeDerivation

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

/-- The underlying `RingCat`-valued presheaf of a presheaf of commutative rings. -/
private abbrev ringPresheaf {C : Type u} [Category.{v} C]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) : Cᵒᵖ ⥤ RingCat.{max u v} :=
  𝒪 ⋙ forget₂ CommRingCat RingCat

/- Domain-style sampling for Lemma 18.33.4:
- primary domain: sheafification of presheaves of modules over a presheaf of commutative rings,
  applied to the canonical presheaf of relative differentials;
- sampled owner declarations:
  `PresheafOfModules.sheafificationRingMap`,
  `PresheafOfModules.moduleSheafification`,
  `SheafOfModules.RingedSite.relativeDifferentials`;
- best owner abstraction: the canonical presheaf-side module sheafification owner
  `PresheafOfModules.moduleSheafification` built from
  `PresheafOfModules.sheafificationRingMap`, together with the sheaf-side
  relative-differentials owner `Ω(φ)`;
- primitive data: a morphism `φ : O₁ ⟶ O₂` of presheaves of commutative rings and its sheafified
  morphism `(presheafToSheaf J CommRingCat).map φ`;
- derived API: the canonical comparison isomorphism identifying the module sheafification of the
  presheaf-level relative differentials with the relative-differentials sheaf of the sheafified
  morphism.

Source/core/bridge triage:
- `core/canonical`: `PresheafOfModules.moduleSheafification`,
  `PresheafOfModules.sheafificationRingMap`, and
  `SheafOfModules.RingedSite.relativeDifferentials`;
- `bridge/view`: the comparison isomorphism in this file.

This item is therefore a bridge theorem. Its public statement should use the chapter's canonical
module-sheafification owner and ring-map owner, rather than re-expanding them locally. -/

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable (φ : O₁ ⟶ O₂)

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/-- Helper for Lemma 18.33.4: the sheaf of relative differentials of a morphism of sheaves of
commutative rings on the site. -/
private abbrev relativeDifferentials
    {S₁ S₂ : Sheaf J CommRingCat.{max u v}} (ψ : S₁ ⟶ S₂) :
    Mod(S₂) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf J S₂).obj)).obj
    (relativeDifferentials' ψ.hom)

local notation:max "Ω(" ψ ")" =>
  relativeDifferentials (J := J) ψ

/-- Helper for Lemma 18.33.4: the universal derivation into the sheaf of relative differentials
for a sheaf morphism on the site. -/
private def relativeDifferential
    {S₁ S₂ : Sheaf J CommRingCat.{max u v}} (ψ : S₁ ⟶ S₂) :
    Der[ψ ; Ω(ψ)] :=
  (derivation' ψ.hom).postcomp
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J S₂).obj)).unit.app
      (relativeDifferentials' ψ.hom))

/-- Helper for Lemma 18.33.4: the morphism induced from a target derivation by the universal
property of the sheaf of relative differentials. -/
private def relativeDifferentialDesc
    {S₁ S₂ : Sheaf J CommRingCat.{max u v}}
    (ψ : S₁ ⟶ S₂) {F : Mod(S₂)} (D : Der[ψ ; F]) :
    Ω(ψ) ⟶ F :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J S₂).obj)).symm
    ((isUniversal' ψ.hom).desc D)

/-- Helper for Lemma 18.33.4: under the sheafification adjunction, a morphism out of the sheaf of
relative differentials is computed by composing with the sheafification unit. -/
private theorem sheafificationHomEquiv_relativeDifferentials
    {S₁ S₂ : Sheaf J CommRingCat.{max u v}}
    (ψ : S₁ ⟶ S₂) {F : Mod(S₂)} (f : Ω(ψ) ⟶ F) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J S₂).obj) f =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J S₂).obj)).unit.app
        (relativeDifferentials' ψ.hom)) ≫ f.val := by
  ext X x
  rfl

/-- Helper for Lemma 18.33.4: the descended morphism factors the target derivation through the
universal derivation. -/
private theorem relativeDifferentialDesc_fac
    {S₁ S₂ : Sheaf J CommRingCat.{max u v}}
    (ψ : S₁ ⟶ S₂) {F : Mod(S₂)} (D : Der[ψ ; F]) :
    (relativeDifferential (J := J) ψ).postcomp
        (relativeDifferentialDesc (J := J) ψ D).val =
      D := by
  have hcomp :
      (relativeDifferential (J := J) ψ).postcomp
          (relativeDifferentialDesc (J := J) ψ D).val =
        (derivation' ψ.hom).postcomp
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J S₂).obj)).unit.app
            (relativeDifferentials' ψ.hom)) ≫
            (relativeDifferentialDesc (J := J) ψ D).val) := by
    rw [relativeDifferential]
    ext X b
    rfl
  have hdesc :
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J S₂).obj)).unit.app
        (relativeDifferentials' ψ.hom)) ≫
          (relativeDifferentialDesc (J := J) ψ D).val =
        (isUniversal' ψ.hom).desc D := by
    have hdesc₀ :=
      (sheafificationHomEquiv_relativeDifferentials (J := J) ψ
        (f := relativeDifferentialDesc (J := J) ψ D)).symm
    rw [relativeDifferentialDesc] at hdesc₀
    rw [Equiv.apply_symm_apply] at hdesc₀
    exact hdesc₀
  have hfac :
      (derivation' ψ.hom).postcomp
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J S₂).obj)).unit.app
            (relativeDifferentials' ψ.hom)) ≫
            (relativeDifferentialDesc (J := J) ψ D).val) =
        D := by
    exact (congrArg (fun f ↦ (derivation' ψ.hom).postcomp f) hdesc).trans
      ((isUniversal' ψ.hom).fac D)
  exact hcomp.trans hfac

/-- Helper for Lemma 18.33.4: a morphism out of the sheaf of relative differentials is determined
by its postcomposition with the universal derivation. -/
private theorem relativeDifferential_postcomp_injective
    {S₁ S₂ : Sheaf J CommRingCat.{max u v}}
    (ψ : S₁ ⟶ S₂) {F : Mod(S₂)}
    ⦃α β : Ω(ψ) ⟶ F⦄
    (h : (relativeDifferential (J := J) ψ).postcomp α.val =
      (relativeDifferential (J := J) ψ).postcomp β.val) :
    α = β := by
  have hα_unit :
      (derivation' ψ.hom).postcomp
          (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J S₂).obj) α) =
        (derivation' ψ.hom).postcomp
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J S₂).obj)).unit.app
            (relativeDifferentials' ψ.hom)) ≫ α.val) := by
    exact congrArg (fun f ↦ (derivation' ψ.hom).postcomp f)
      (sheafificationHomEquiv_relativeDifferentials (J := J) ψ (f := α))
  have hβ_unit :
      (derivation' ψ.hom).postcomp
          (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J S₂).obj) β) =
        (derivation' ψ.hom).postcomp
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J S₂).obj)).unit.app
            (relativeDifferentials' ψ.hom)) ≫ β.val) := by
    exact congrArg (fun f ↦ (derivation' ψ.hom).postcomp f)
      (sheafificationHomEquiv_relativeDifferentials (J := J) ψ (f := β))
  have hα_comp :
      (derivation' ψ.hom).postcomp
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J S₂).obj)).unit.app
            (relativeDifferentials' ψ.hom)) ≫ α.val) =
        (relativeDifferential (J := J) ψ).postcomp α.val := by
    rw [relativeDifferential]
    ext X b
    rfl
  have hβ_comp :
      (derivation' ψ.hom).postcomp
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J S₂).obj)).unit.app
            (relativeDifferentials' ψ.hom)) ≫ β.val) =
        (relativeDifferential (J := J) ψ).postcomp β.val := by
    rw [relativeDifferential]
    ext X b
    rfl
  have hα' :
      (derivation' ψ.hom).postcomp
          (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J S₂).obj) α) =
        (relativeDifferential (J := J) ψ).postcomp α.val :=
    hα_unit.trans hα_comp
  have hβ' :
      (derivation' ψ.hom).postcomp
          (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J S₂).obj) β) =
        (relativeDifferential (J := J) ψ).postcomp β.val :=
    hβ_unit.trans hβ_comp
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J S₂).obj)).injective
  apply (isUniversal' ψ.hom).postcomp_injective
  exact hα'.trans (h.trans hβ'.symm)

/-- Local owner for the commutative-ring-valued sheafification of a presheaf of commutative
rings. -/
abbrev relativeDifferentialsCommRingSheafification
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{max u v}]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    Sheaf J CommRingCat.{max u v} :=
  (presheafToSheaf J CommRingCat.{max u v}).obj 𝒪

/-- Local comparison from ring-valued sheafification to the forgotten sheafification of
commutative rings. -/
noncomputable abbrev relativeDifferentialsSheafificationRingBridge
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify J CommRingCat.{max u v}]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    (presheafToSheaf J RingCat.{max u v}).obj (ringPresheaf 𝒪) ⟶
      ringSheaf J (relativeDifferentialsCommRingSheafification J 𝒪) :=
  (CategoryTheory.sheafComposeNatTrans J (forget₂ CommRingCat RingCat)
    (CategoryTheory.sheafificationAdjunction J CommRingCat.{max u v})
    (CategoryTheory.sheafificationAdjunction J RingCat.{max u v})).app 𝒪

/-- Local owner for the canonical ring map `𝒪 ⟶ 𝒪^#` after forgetting commutativity. -/
abbrev relativeDifferentialsSheafificationRingMap
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify J CommRingCat.{max u v}]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    ringPresheaf 𝒪 ⟶
      (ringSheaf J (relativeDifferentialsCommRingSheafification J 𝒪)).obj :=
  CategoryTheory.toSheafify J (ringPresheaf 𝒪) ≫
    (sheafToPresheaf J RingCat.{max u v}).map
      (relativeDifferentialsSheafificationRingBridge J 𝒪)

/-- The local sheafification ring map is the forgotten commutative-ring sheafification unit. -/
private theorem relativeDifferentialsSheafificationRingMap_eq_whiskerRight
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify J CommRingCat.{max u v}]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    relativeDifferentialsSheafificationRingMap J 𝒪 =
      Functor.whiskerRight
        (show 𝒪 ⟶ (relativeDifferentialsCommRingSheafification J 𝒪).obj from
          CategoryTheory.toSheafify J 𝒪)
        (forget₂ CommRingCat RingCat) := by
  simpa [relativeDifferentialsSheafificationRingMap,
    relativeDifferentialsSheafificationRingBridge,
    relativeDifferentialsCommRingSheafification, ringPresheaf, ringSheaf] using
    (CategoryTheory.sheafComposeNatTrans_fac J (forget₂ CommRingCat RingCat)
      (CategoryTheory.sheafificationAdjunction J CommRingCat.{max u v})
      (CategoryTheory.sheafificationAdjunction J RingCat.{max u v}) 𝒪)

/-- The local sheafification ring map is locally injective. -/
instance relativeDifferentialsSheafificationRingMap_isLocallyInjective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify J CommRingCat.{max u v}]
    [J.WEqualsLocallyBijective CommRingCat.{max u v}]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    Presheaf.IsLocallyInjective J (relativeDifferentialsSheafificationRingMap J 𝒪) := by
  let η : 𝒪 ⟶ (relativeDifferentialsCommRingSheafification J 𝒪).obj :=
    CategoryTheory.toSheafify J 𝒪
  have hη : Presheaf.IsLocallyInjective J η :=
    (J.W_toSheafify (A := CommRingCat.{max u v}) 𝒪).isLocallyInjective
  have hηForget :
      Presheaf.IsLocallyInjective J
        (Functor.whiskerRight (Functor.whiskerRight η (forget₂ CommRingCat RingCat))
          (CategoryTheory.forget RingCat)) := by
    simpa using ((Presheaf.isLocallyInjective_forget_iff (J := J) (φ := η)).2 hη)
  have hηRing :
      Presheaf.IsLocallyInjective J (Functor.whiskerRight η (forget₂ CommRingCat RingCat)) :=
    (Presheaf.isLocallyInjective_forget_iff
      (J := J) (φ := Functor.whiskerRight η (forget₂ CommRingCat RingCat))).1 hηForget
  simpa [relativeDifferentialsSheafificationRingMap_eq_whiskerRight (J := J) 𝒪, η] using hηRing

/-- The local sheafification ring map is locally surjective. -/
instance relativeDifferentialsSheafificationRingMap_isLocallySurjective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify J CommRingCat.{max u v}]
    [J.WEqualsLocallyBijective CommRingCat.{max u v}]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    Presheaf.IsLocallySurjective J (relativeDifferentialsSheafificationRingMap J 𝒪) := by
  let η : 𝒪 ⟶ (relativeDifferentialsCommRingSheafification J 𝒪).obj :=
    CategoryTheory.toSheafify J 𝒪
  have hη : Presheaf.IsLocallySurjective J η :=
    (J.W_toSheafify (A := CommRingCat.{max u v}) 𝒪).isLocallySurjective
  have hηForget :
      Presheaf.IsLocallySurjective J
        (Functor.whiskerRight (Functor.whiskerRight η (forget₂ CommRingCat RingCat))
          (CategoryTheory.forget RingCat)) := by
    simpa using ((Presheaf.isLocallySurjective_iff_whisker_forget (J := J) η).1 hη)
  have hηRing :
      Presheaf.IsLocallySurjective J (Functor.whiskerRight η (forget₂ CommRingCat RingCat)) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget
      (J := J) (Functor.whiskerRight η (forget₂ CommRingCat RingCat))).2 hηForget
  simpa [relativeDifferentialsSheafificationRingMap_eq_whiskerRight (J := J) 𝒪, η] using hηRing

/-- Local owner for sheafifying presheaves of modules along `𝒪 ⟶ 𝒪^#`. -/
abbrev relativeDifferentialsModuleSheafification
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify J CommRingCat.{max u v}]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    PresheafOfModules (ringPresheaf 𝒪) ⥤
      ringedSiteModuleCategory J
        (relativeDifferentialsCommRingSheafification J 𝒪) :=
  PresheafOfModules.sheafification
    (relativeDifferentialsSheafificationRingMap J 𝒪)

local macro "PresheafOfModules.commRingSheafification" : term =>
  `(relativeDifferentialsCommRingSheafification)

local macro "PresheafOfModules.sheafificationRingMap" : term =>
  `(relativeDifferentialsSheafificationRingMap)

local macro "PresheafOfModules.moduleSheafification" : term =>
  `(relativeDifferentialsModuleSheafification)

private abbrev sheafifiedMorphism :
    PresheafOfModules.commRingSheafification J O₁ ⟶
      PresheafOfModules.commRingSheafification J O₂ :=
  (presheafToSheaf J CommRingCat.{max u v}).map φ

private abbrev sheafifiedRelativeDifferentials :
    PresheafOfModules
      (ringSheaf J (PresheafOfModules.commRingSheafification J O₂)).obj :=
  relativeDifferentials' (sheafifiedMorphism J O₁ O₂ φ).hom

private abbrev presheafRestrictScalars :
    PresheafOfModules (ringSheaf J (PresheafOfModules.commRingSheafification J O₂)).obj ⥤
      PresheafOfModules (ringPresheaf O₂) :=
  PresheafOfModules.restrictScalars (PresheafOfModules.sheafificationRingMap J O₂)

/-- Helper for Lemma 18.33.4: the raw restriction-of-scalars functor along the sheafification unit
before identifying it with `PresheafOfModules.sheafificationRingMap`. -/
private abbrev presheafRestrictScalarsAlongUnit :
    PresheafOfModules (ringSheaf J (PresheafOfModules.commRingSheafification J O₂)).obj ⥤
      PresheafOfModules (ringPresheaf O₂) :=
  PresheafOfModules.restrictScalars
    (Functor.whiskerRight
      (show O₂ ⟶ (PresheafOfModules.commRingSheafification J O₂).obj from
        CategoryTheory.toSheafify J O₂)
      (forget₂ CommRingCat RingCat))

/-- Helper for Lemma 18.33.4: `sheafificationRingMap` is the forgotten CommRing-valued
sheafification unit. -/
private theorem sheafificationRingMap_eq_whiskerRight
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    PresheafOfModules.sheafificationRingMap J 𝒪 =
      Functor.whiskerRight
        (show 𝒪 ⟶ (PresheafOfModules.commRingSheafification J 𝒪).obj from
          CategoryTheory.toSheafify J 𝒪)
        (forget₂ CommRingCat RingCat) := by
  simpa using relativeDifferentialsSheafificationRingMap_eq_whiskerRight (J := J) 𝒪

/-- The sectionwise commutativity relation comparing `φ` with its sheafification. -/
private theorem sheafifiedRelativeDifferentialsSquare_app (X : Cᵒᵖ) :
    (CategoryTheory.toSheafify J O₁).app X ≫
        (sheafifiedMorphism J O₁ O₂ φ).hom.app X =
      φ.app X ≫ (CategoryTheory.toSheafify J O₂).app X := by
  exact NatTrans.congr_app (CategoryTheory.toSheafify_naturality J φ).symm X

/-- Helper for Lemma 18.33.4: objectwise, the ring map underlying
`PresheafOfModules.sheafificationRingMap` is exactly the forgotten sheafification unit. -/
private theorem sheafificationRingMapAppHom
    (X : Cᵒᵖ) :
    ((PresheafOfModules.sheafificationRingMap J O₂).app X).hom =
      ((CategoryTheory.toSheafify J O₂).app X).hom := by
  -- Proof comment: evaluate the natural-transformation comparison at `X` and forget from
  -- `RingCat` morphisms to ring homomorphisms.
  simpa using congrArg RingCat.Hom.hom
    (NatTrans.congr_app (sheafificationRingMap_eq_whiskerRight (J := J) O₂) X)

-- Proof sketch: both sides are morphisms out of the objectwise Kähler differentials on `O₂(X)`.
-- Equality on generators `d b` reduces to the naturality of `toSheafify` together with
-- `CommRingCat.KaehlerDifferential.map_d`.
/-- Helper for Lemma 18.33.4: objectwise, the Kähler comparison for `φ` lands in the restricted
sheafified relative differentials presheaf after transporting the codomain from `toSheafify` to
`sheafificationRingMap`. -/
private noncomputable abbrev sheafifiedRelativeDifferentialsMapAppAlongUnit
    (X : Cᵒᵖ) :
    (relativeDifferentials' φ).obj X ⟶
      (ModuleCat.restrictScalars (((CategoryTheory.toSheafify J O₂).app X).hom)).obj
        ((sheafifiedRelativeDifferentials J O₁ O₂ φ).obj X) :=
  CommRingCat.KaehlerDifferential.map
    (sheafifiedRelativeDifferentialsSquare_app (J := J) (O₁ := O₁) (O₂ := O₂) (φ := φ) X)

/-- Helper for Lemma 18.33.4: objectwise, the Kähler comparison for `φ` lands in the restricted
sheafified relative differentials presheaf after transporting the codomain from `toSheafify` to
`sheafificationRingMap`. -/
private theorem sheafifiedRelativeDifferentialsMapAppAlongUnit_obj
    (X : Cᵒᵖ) :
    (ModuleCat.restrictScalars (((CategoryTheory.toSheafify J O₂).app X).hom)).obj
        ((sheafifiedRelativeDifferentials J O₁ O₂ φ).obj X) =
      ((presheafRestrictScalars J O₂).obj
        (sheafifiedRelativeDifferentials J O₁ O₂ φ)).obj X := by
  -- Proof comment: identify the two scalar ring maps at `X`, then transport the restricted
  -- module object along that objectwise equality.
  simpa [presheafRestrictScalars] using
    congrArg
      (fun r ↦
        (ModuleCat.restrictScalars r).obj
          ((sheafifiedRelativeDifferentials J O₁ O₂ φ).obj X))
      (sheafificationRingMapAppHom (J := J) (O₂ := O₂) X).symm

/-- Helper for Lemma 18.33.4: objectwise, the Kähler comparison for `φ` lands in the restricted
sheafified relative differentials presheaf after transporting the codomain from `toSheafify` to
`sheafificationRingMap`. -/
private theorem restrictScalars_eqToIso_hom_apply
    {R S : Type*} [CommRing R] [CommRing S]
    {u v : R →+* S} (h : u = v) (M : ModuleCat S)
    (m : (ModuleCat.restrictScalars u).obj M) :
    ((eqToIso (congrArg (fun w ↦ (ModuleCat.restrictScalars w).obj M) h)).hom) m = m := by
  -- Proof comment: after reducing to the reflexive ring-map equality, the transport is the
  -- identity on sections by definition.
  cases h
  rfl

/-- Helper for Lemma 18.33.4: objectwise, the Kähler comparison for `φ` lands in the restricted
sheafified relative differentials presheaf after transporting the codomain from `toSheafify` to
`sheafificationRingMap`. -/
private noncomputable def sheafifiedRelativeDifferentialsMapApp
    (X : Cᵒᵖ) :
    (relativeDifferentials' φ).obj X ⟶
      ((presheafRestrictScalars J O₂).obj
        (sheafifiedRelativeDifferentials J O₁ O₂ φ)).obj X :=
  -- Proof comment: postcompose the raw comparison with the objectwise identification of the two
  -- restricted-scalars codomains.
  sheafifiedRelativeDifferentialsMapAppAlongUnit
      (J := J) (O₁ := O₁) (O₂ := O₂) (φ := φ) X ≫
    eqToHom
      (sheafifiedRelativeDifferentialsMapAppAlongUnit_obj
        (J := J) (O₁ := O₁) (O₂ := O₂) (φ := φ) X)

/-- Helper for Lemma 18.33.4: the transported objectwise comparison still sends `d(f)` to
`d((toSheafify f))`. -/
private theorem sheafifiedRelativeDifferentialsMapApp_d
    (X : Cᵒᵖ) (b : O₂.obj X) :
    (ConcreteCategory.hom (sheafifiedRelativeDifferentialsMapApp J O₁ O₂ φ X))
      (CommRingCat.KaehlerDifferential.d b) =
        CommRingCat.KaehlerDifferential.d ((CategoryTheory.toSheafify J O₂).app X b) := by
  sorry

/-- Helper for Lemma 18.33.4: before transporting the codomain from `toSheafify` to
`sheafificationRingMap`, the sectionwise Kähler comparison is natural in the site variable. -/
private theorem sheafifiedRelativeDifferentialsMapAppAlongUnit_naturality
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (relativeDifferentials' φ).map f ≫
        (ModuleCat.restrictScalars
            (((O₂ ⋙ forget₂ CommRingCat RingCat).map f).hom)).map
          (sheafifiedRelativeDifferentialsMapAppAlongUnit J O₁ O₂ φ Y) =
      sheafifiedRelativeDifferentialsMapAppAlongUnit J O₁ O₂ φ X ≫
        ((presheafRestrictScalarsAlongUnit J O₂).obj
          (sheafifiedRelativeDifferentials J O₁ O₂ φ)).map f := by
  apply CommRingCat.KaehlerDifferential.ext
  intro b
  have htoSheafify :
      (CategoryTheory.toSheafify J O₂).app Y ((O₂ ⋙ forget₂ CommRingCat RingCat).map f b) =
        (ringSheaf J (PresheafOfModules.commRingSheafification J O₂)).obj.map f
          ((CategoryTheory.toSheafify J O₂).app X b) := by
    exact DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom ((CategoryTheory.toSheafify J O₂).naturality f)) b
  -- Proof comment: both composites are determined by the image of the generator `d b`.
  have h₁ :
      (ConcreteCategory.hom (sheafifiedRelativeDifferentialsMapAppAlongUnit J O₁ O₂ φ Y))
          ((ConcreteCategory.hom ((relativeDifferentials' φ).map f))
            (CommRingCat.KaehlerDifferential.d b)) =
        (ConcreteCategory.hom (sheafifiedRelativeDifferentialsMapAppAlongUnit J O₁ O₂ φ Y))
          (CommRingCat.KaehlerDifferential.d ((O₂ ⋙ forget₂ CommRingCat RingCat).map f b)) := by
    congr 1
    simpa using relativeDifferentials'_map_d φ f b
  have h₂ :
      (ConcreteCategory.hom (sheafifiedRelativeDifferentialsMapAppAlongUnit J O₁ O₂ φ Y))
          (CommRingCat.KaehlerDifferential.d ((O₂ ⋙ forget₂ CommRingCat RingCat).map f b)) =
        CommRingCat.KaehlerDifferential.d
          ((CategoryTheory.toSheafify J O₂).app Y
            ((O₂ ⋙ forget₂ CommRingCat RingCat).map f b)) := by
    change (ConcreteCategory.hom
        (CommRingCat.KaehlerDifferential.map
          (sheafifiedRelativeDifferentialsSquare_app (J := J) (O₁ := O₁) (O₂ := O₂) (φ := φ) Y)))
        (CommRingCat.KaehlerDifferential.d ((O₂ ⋙ forget₂ CommRingCat RingCat).map f b)) =
      CommRingCat.KaehlerDifferential.d
        ((CategoryTheory.toSheafify J O₂).app Y
          ((O₂ ⋙ forget₂ CommRingCat RingCat).map f b))
    exact CommRingCat.KaehlerDifferential.map_d
      (sheafifiedRelativeDifferentialsSquare_app
        (J := J) (O₁ := O₁) (O₂ := O₂) (φ := φ) Y)
      ((O₂ ⋙ forget₂ CommRingCat RingCat).map f b)
  have h₃ :
      CommRingCat.KaehlerDifferential.d
          ((CategoryTheory.toSheafify J O₂).app Y
            ((O₂ ⋙ forget₂ CommRingCat RingCat).map f b)) =
        (ConcreteCategory.hom
          (((presheafRestrictScalarsAlongUnit J O₂).obj
            (sheafifiedRelativeDifferentials J O₁ O₂ φ)).map f))
          (CommRingCat.KaehlerDifferential.d
            ((CategoryTheory.toSheafify J O₂).app X b)) := by
    rw [htoSheafify]
    symm
    simpa using relativeDifferentials'_map_d (sheafifiedMorphism J O₁ O₂ φ).hom f
      ((CategoryTheory.toSheafify J O₂).app X b)
  have h₄ :
      (ConcreteCategory.hom
          (((presheafRestrictScalarsAlongUnit J O₂).obj
            (sheafifiedRelativeDifferentials J O₁ O₂ φ)).map f))
          (CommRingCat.KaehlerDifferential.d
            ((CategoryTheory.toSheafify J O₂).app X b)) =
        (ConcreteCategory.hom
          (((presheafRestrictScalarsAlongUnit J O₂).obj
            (sheafifiedRelativeDifferentials J O₁ O₂ φ)).map f))
          ((ConcreteCategory.hom (sheafifiedRelativeDifferentialsMapAppAlongUnit J O₁ O₂ φ X))
            (CommRingCat.KaehlerDifferential.d b)) := by
    congr 1
    symm
    change (ConcreteCategory.hom
        (CommRingCat.KaehlerDifferential.map
          (sheafifiedRelativeDifferentialsSquare_app (J := J) (O₁ := O₁) (O₂ := O₂) (φ := φ) X)))
        (CommRingCat.KaehlerDifferential.d b) =
      CommRingCat.KaehlerDifferential.d ((CategoryTheory.toSheafify J O₂).app X b)
    exact CommRingCat.KaehlerDifferential.map_d
      (sheafifiedRelativeDifferentialsSquare_app
        (J := J) (O₁ := O₁) (O₂ := O₂) (φ := φ) X)
      b
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- The objectwise sheafification comparison on relative differentials is natural in the site
variable. -/
private theorem sheafifiedRelativeDifferentialsMapApp_naturality
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (relativeDifferentials' φ).map f ≫
        (ModuleCat.restrictScalars
            (((O₂ ⋙ forget₂ CommRingCat RingCat).map f).hom)).map
          (sheafifiedRelativeDifferentialsMapApp J O₁ O₂ φ Y) =
      sheafifiedRelativeDifferentialsMapApp J O₁ O₂ φ X ≫
        ((presheafRestrictScalars J O₂).obj
          (sheafifiedRelativeDifferentials J O₁ O₂ φ)).map f := by
  apply CommRingCat.KaehlerDifferential.ext
  intro b
  have htoSheafify :
      (CategoryTheory.toSheafify J O₂).app Y ((O₂ ⋙ forget₂ CommRingCat RingCat).map f b) =
        (ringSheaf J (PresheafOfModules.commRingSheafification J O₂)).obj.map f
          ((CategoryTheory.toSheafify J O₂).app X b) := by
    exact DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom ((CategoryTheory.toSheafify J O₂).naturality f)) b
  -- Proof comment: both composites are determined by the image of the generator `d b`.
  have h₁ :
      (ConcreteCategory.hom (sheafifiedRelativeDifferentialsMapApp J O₁ O₂ φ Y))
          ((ConcreteCategory.hom ((relativeDifferentials' φ).map f))
            (CommRingCat.KaehlerDifferential.d b)) =
        (ConcreteCategory.hom (sheafifiedRelativeDifferentialsMapApp J O₁ O₂ φ Y))
          (CommRingCat.KaehlerDifferential.d ((O₂ ⋙ forget₂ CommRingCat RingCat).map f b)) := by
    congr 1
    simpa using relativeDifferentials'_map_d φ f b
  have h₂ :
      (ConcreteCategory.hom (sheafifiedRelativeDifferentialsMapApp J O₁ O₂ φ Y))
          (CommRingCat.KaehlerDifferential.d ((O₂ ⋙ forget₂ CommRingCat RingCat).map f b)) =
        CommRingCat.KaehlerDifferential.d
          ((CategoryTheory.toSheafify J O₂).app Y
            ((O₂ ⋙ forget₂ CommRingCat RingCat).map f b)) := by
    simpa using
      sheafifiedRelativeDifferentialsMapApp_d
        (J := J) (O₁ := O₁) (O₂ := O₂) (φ := φ) Y
        ((O₂ ⋙ forget₂ CommRingCat RingCat).map f b)
  have h₃ :
      CommRingCat.KaehlerDifferential.d
          ((CategoryTheory.toSheafify J O₂).app Y
            ((O₂ ⋙ forget₂ CommRingCat RingCat).map f b)) =
        (ConcreteCategory.hom
          (((presheafRestrictScalars J O₂).obj
            (sheafifiedRelativeDifferentials J O₁ O₂ φ)).map f))
          (CommRingCat.KaehlerDifferential.d
            ((CategoryTheory.toSheafify J O₂).app X b)) := by
    rw [htoSheafify]
    symm
    simpa using relativeDifferentials'_map_d (sheafifiedMorphism J O₁ O₂ φ).hom f
      ((CategoryTheory.toSheafify J O₂).app X b)
  have h₄ :
      (ConcreteCategory.hom
          (((presheafRestrictScalars J O₂).obj
            (sheafifiedRelativeDifferentials J O₁ O₂ φ)).map f))
          (CommRingCat.KaehlerDifferential.d
            ((CategoryTheory.toSheafify J O₂).app X b)) =
        (ConcreteCategory.hom
          (((presheafRestrictScalars J O₂).obj
            (sheafifiedRelativeDifferentials J O₁ O₂ φ)).map f))
          ((ConcreteCategory.hom (sheafifiedRelativeDifferentialsMapApp J O₁ O₂ φ X))
            (CommRingCat.KaehlerDifferential.d b)) := by
    congr 1
    symm
    exact sheafifiedRelativeDifferentialsMapApp_d
      (J := J) (O₁ := O₁) (O₂ := O₂) (φ := φ) X b
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- The presheaf-level comparison on relative differentials induced by sheafifying `φ`. -/
private noncomputable def sheafifiedRelativeDifferentialsMapPresheaf :
    relativeDifferentials' φ ⟶
      (presheafRestrictScalars J O₂).obj
        (sheafifiedRelativeDifferentials J O₁ O₂ φ) where
  app X := sheafifiedRelativeDifferentialsMapApp J O₁ O₂ φ X
  naturality f := sheafifiedRelativeDifferentialsMapApp_naturality J O₁ O₂ φ f

-- Proof sketch: descend the presheaf comparison map through the module-sheafification adjunction,
-- then use the sheafification unit for the sheaf-level owner `Ω(O₁^# ⟶ O₂^#)`.
/-- The canonical comparison morphism from the sheafification of the presheaf-level relative
differentials to the sheaf of relative differentials of the sheafified morphism. -/
noncomputable def moduleSheafification_relativeDifferentials_comparison :
    (PresheafOfModules.moduleSheafification J O₂).obj (relativeDifferentials' φ) ⟶
      Ω((presheafToSheaf J CommRingCat.{max u v}).map φ) :=
  (PresheafOfModules.sheafificationHomEquiv
      (PresheafOfModules.sheafificationRingMap J O₂)).symm
    (sheafifiedRelativeDifferentialsMapPresheaf J O₁ O₂ φ ≫
      (presheafRestrictScalars J O₂).map
        ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (ringSheaf J (PresheafOfModules.commRingSheafification J O₂)).obj)).unit.app
          (sheafifiedRelativeDifferentials J O₁ O₂ φ)))

-- Proof sketch: both sides are obtained by sheafifying the objectwise cokernel presentation of
-- Kähler differentials from `18.33.2.1`. Exactness of module sheafification identifies the
-- resulting presentations, and hence the comparison morphism is an isomorphism.
/-- The canonical comparison morphism of Lemma 18.33.4 is an isomorphism. -/
@[instance] theorem moduleSheafification_relativeDifferentials_comparison_isIso :
    IsIso (moduleSheafification_relativeDifferentials_comparison J O₁ O₂ φ) := by
  sorry

/-- Lemma 18.33.4: for a morphism `φ : O₁ ⟶ O₂` of presheaves of commutative rings on a site, the
sheaf of relative differentials of the sheafified morphism `O₁^# ⟶ O₂^#` is canonically
isomorphic to the module sheafification of the presheaf `U ↦ Ω[O₂(U)⁄O₁(U)]`. -/
noncomputable abbrev moduleSheafification_relativeDifferentials_iso :
    (PresheafOfModules.moduleSheafification J O₂).obj (relativeDifferentials' φ) ≅
      Ω((presheafToSheaf J CommRingCat.{max u v}).map φ) :=
  asIso (moduleSheafification_relativeDifferentials_comparison J O₁ O₂ φ)

end SheafOfModules.RingedSite
