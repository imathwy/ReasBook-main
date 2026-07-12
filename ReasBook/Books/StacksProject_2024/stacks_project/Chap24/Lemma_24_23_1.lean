import StacksProject_2024.Chap18.Lemma_18_19_2
import StacksProject_2024.Chap21.Definition_21_17_2
import StacksProject_2024.Chap24.Definition_24_13_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ M : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj M).Additive]

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex ModO ℤ
local notation "DGAO" => @SheafOfModules.RingedSite.DifferentialGradedAlgebra C _ J _ 𝒪 _

-- Semantic search note: `lean_leansearch` was unavailable in this runner (HTTP 521), so the
-- owner/API choice here was fixed against the local Chapter 18 localization functors, the
-- Chapter 21 `IsTermwiseFlat`/`IsKFlat` owners, and the Chapter 24 differential graded algebra
-- owner in `Definition_24_13_1.lean`.

/-- The localized restriction functor on `\mathcal O`-modules preserves zero morphisms, so it
lifts to cochain complexes. -/
private instance localizedRestriction_preservesZeroMorphisms
    (U : C) :
    (ringedSiteLocalizedRestriction J 𝒪 U).PreservesZeroMorphisms := by
  dsimp [ringedSiteLocalizedRestriction]
  refine ⟨fun _ _ ↦ ?_⟩
  rfl

/-- The underlying cochain complex formalizing `j_! \mathcal A_U`: first restrict the underlying
complex of `\mathcal A` to the localized ringed site `(\mathcal C/U, \mathcal O_U)`, then extend
that localized complex by zero back to `(\mathcal C, \mathcal O)`. -/
abbrev localizedAlgebraExtensionByZeroComplex
    (𝒜 : DGAO) (U : C) : CpxO :=
  ((ringedSiteLocalizedExtensionByZero J 𝒪 U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((ringedSiteLocalizedRestriction J 𝒪 U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      𝒜.toComplex)

/-- The source-facing helper `localizedAlgebraExtensionByZeroComplex` is the extension by zero of
the localized underlying cochain complex of `\mathcal A`. -/
theorem localizedAlgebraExtensionByZeroComplex_def
    (𝒜 : DGAO) (U : C) :
    localizedAlgebraExtensionByZeroComplex 𝒜 U =
      ((ringedSiteLocalizedExtensionByZero J 𝒪 U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ringedSiteLocalizedRestriction J 𝒪 U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          𝒜.toComplex) := sorry

/-- The `RingCat`-valued structure map underlying a site-presented pullback of sheaves of
commutative rings. This local bridge avoids importing the heavier Chapter 21 pullback file. -/
private abbrev pullbackStructureMap
    {D : Type u} [Category.{v} D] {JD : GrothendieckTopology D}
    [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (F : C ⥤ D) [Functor.IsContinuous F J JD]
    {𝒪' : Sheaf JD CommRingCat.{max u v}}
    (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).obj 𝒪') :
    ringSheaf J 𝒪 ⟶
      (F.sheafPushforwardContinuous RingCat.{max u v} J JD).obj (ringSheaf JD 𝒪') :=
  (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map φ

/-- The pullback functor on module sheaves for a site-presented morphism of ringed sites. This is
the local bridge needed to state pullback stability in Lemma 24.23.1 without the heavier shared
Chapter 21 bridge import. -/
private abbrev pullbackFunctor
    {D : Type u} [Category.{v} D] {JD : GrothendieckTopology D}
    [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (F : C ⥤ D) [Functor.IsContinuous F J JD]
    {𝒪' : Sheaf JD CommRingCat.{max u v}}
    (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).obj 𝒪')
    [(SheafOfModules.pushforward (pullbackStructureMap F φ)).IsRightAdjoint]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).IsRightAdjoint] :
    ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory JD 𝒪' :=
  SheafOfModules.pullback (pullbackStructureMap F φ)

/-- Lemma 24.23.1: let `(\mathcal C, \mathcal O)` be a ringed site, let `\mathcal A` be a sheaf
of differential graded algebras on it, and let `U` be an object of `\mathcal C`. Then
`j_! \mathcal A_U` is a good differential graded `\mathcal A`-module. In this item the goodness
condition is stated directly for the underlying cochain complex as termwise flatness, K-flatness,
and stability of those properties under every site-presented pullback. -/
@[stacks 0FSB]
class isGood_localizedAlgebraExtensionByZeroComplex
    (𝒜 : DGAO) (U : C) : Prop where
  /-- The extension by zero of the localized complex is termwise flat. -/
  termwiseFlat :
    CochainComplex.IsTermwiseFlat (localizedAlgebraExtensionByZeroComplex 𝒜 U)
  /-- The extension by zero of the localized complex is K-flat. -/
  kFlat :
    (localizedAlgebraExtensionByZeroComplex 𝒜 U).IsKFlat
  /-- The same flatness properties persist after every site-presented pullback. -/
  pullback :
      ∀ {D : Type u} [Category.{v} D] {JD : GrothendieckTopology D}
        [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
        [HasWeakSheafify JD AddCommGrpCat.{max u v}]
        [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
        (F : C ⥤ D) [Functor.IsContinuous F J JD]
        {𝒪' : Sheaf JD CommRingCat.{max u v}}
        (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).obj 𝒪')
        [(F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).IsRightAdjoint]
        [(SheafOfModules.pushforward
          (pullbackStructureMap F φ)).IsRightAdjoint]
        [(pullbackFunctor F φ).PreservesZeroMorphisms]
        [MonoidalCategory (ringedSiteModuleCategory JD 𝒪')]
        [MonoidalPreadditive (ringedSiteModuleCategory JD 𝒪')]
        [(curriedTensor (ringedSiteModuleCategory JD 𝒪')).Additive]
        [∀ M : ringedSiteModuleCategory JD 𝒪',
          ((curriedTensor (ringedSiteModuleCategory JD 𝒪')).obj M).Additive],
        let K := localizedAlgebraExtensionByZeroComplex 𝒜 U
        let K' := (((pullbackFunctor F φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        K'.IsKFlat ∧ CochainComplex.IsTermwiseFlat K'

/-- Constructor instance for the fieldwise form of goodness used by Lemma 24.23.1. -/
instance isGood_localizedAlgebraExtensionByZeroComplex_of_termwiseFlat_kFlat_pullback
    (𝒜 : DGAO) (U : C)
    (termwiseFlat :
      CochainComplex.IsTermwiseFlat (localizedAlgebraExtensionByZeroComplex 𝒜 U))
    (kFlat :
      (localizedAlgebraExtensionByZeroComplex 𝒜 U).IsKFlat)
    (pullback :
      ∀ {D : Type u} [Category.{v} D] {JD : GrothendieckTopology D}
        [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
        [HasWeakSheafify JD AddCommGrpCat.{max u v}]
        [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
        (F : C ⥤ D) [Functor.IsContinuous F J JD]
        {𝒪' : Sheaf JD CommRingCat.{max u v}}
        (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).obj 𝒪')
        [(F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).IsRightAdjoint]
        [(SheafOfModules.pushforward
          (pullbackStructureMap F φ)).IsRightAdjoint]
        [(pullbackFunctor F φ).PreservesZeroMorphisms]
        [MonoidalCategory (ringedSiteModuleCategory JD 𝒪')]
        [MonoidalPreadditive (ringedSiteModuleCategory JD 𝒪')]
        [(curriedTensor (ringedSiteModuleCategory JD 𝒪')).Additive]
        [∀ M : ringedSiteModuleCategory JD 𝒪',
          ((curriedTensor (ringedSiteModuleCategory JD 𝒪')).obj M).Additive],
        CochainComplex.IsKFlat
          (((pullbackFunctor F φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (localizedAlgebraExtensionByZeroComplex 𝒜 U)) ∧
          CochainComplex.IsTermwiseFlat
            (((pullbackFunctor F φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (localizedAlgebraExtensionByZeroComplex 𝒜 U))) :
    isGood_localizedAlgebraExtensionByZeroComplex 𝒜 U where
  termwiseFlat := termwiseFlat
  kFlat := kFlat
  pullback := pullback

/-- The goodness class exposes the termwise-flat and K-flat conditions on the extension by zero of
the localized complex. -/
theorem isGood_localizedAlgebraExtensionByZeroComplex_termwiseFlat_kFlat_spec
    (𝒜 : DGAO) (U : C)
    [h : isGood_localizedAlgebraExtensionByZeroComplex 𝒜 U] :
    CochainComplex.IsTermwiseFlat (localizedAlgebraExtensionByZeroComplex 𝒜 U) ∧
      (localizedAlgebraExtensionByZeroComplex 𝒜 U).IsKFlat :=
  ⟨h.termwiseFlat, h.kFlat⟩

/-- The proposition `isGood_localizedAlgebraExtensionByZeroComplex` expands to termwise flatness,
K-flatness, and pullback stability for the extension by zero of the localized underlying complex
of `\mathcal A`. -/
theorem isGood_localizedAlgebraExtensionByZeroComplex_def
    (𝒜 : DGAO) (U : C) :
    isGood_localizedAlgebraExtensionByZeroComplex 𝒜 U ↔
      let K := localizedAlgebraExtensionByZeroComplex 𝒜 U
      CochainComplex.IsTermwiseFlat K ∧
        K.IsKFlat ∧
          ∀ {D : Type u} [Category.{v} D] {JD : GrothendieckTopology D}
            [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
            [HasWeakSheafify JD AddCommGrpCat.{max u v}]
            [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
            (F : C ⥤ D) [Functor.IsContinuous F J JD]
            {𝒪' : Sheaf JD CommRingCat.{max u v}}
            (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).obj 𝒪')
            [(F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).IsRightAdjoint]
            [(SheafOfModules.pushforward
              (pullbackStructureMap F φ)).IsRightAdjoint]
            [(pullbackFunctor F φ).PreservesZeroMorphisms]
            [MonoidalCategory (ringedSiteModuleCategory JD 𝒪')]
            [MonoidalPreadditive (ringedSiteModuleCategory JD 𝒪')]
            [(curriedTensor (ringedSiteModuleCategory JD 𝒪')).Additive]
            [∀ M : ringedSiteModuleCategory JD 𝒪',
              ((curriedTensor (ringedSiteModuleCategory JD 𝒪')).obj M).Additive],
            let K' := (((pullbackFunctor F φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            K'.IsKFlat ∧ CochainComplex.IsTermwiseFlat K' := sorry

end

end SheafOfModules.RingedSite
