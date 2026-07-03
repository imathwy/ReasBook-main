import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_14_1 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Sheaf

noncomputable section

universe u v

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat.{max u v})]

-- Proof sketch: present the given morphism of ringed topoi by the ringed-site morphism `f`.
-- For any sheaf of sets `K` on the target, compute `H^q(K, f_* ℐ)` on the localized site. After
-- enlarging the site as in Lemma `18.7.2`, this becomes ordinary cohomology of the underlying
-- abelian sheaf of `ℐ` on a site where `f_*` is induced by precomposition. The resulting Čech
-- complexes agree with those for `ℐ`, and Lemma `21.12.3` gives vanishing of positive Čech
-- cohomology because `ℐ` is injective. Lemma `21.10.9` then upgrades that Čech vanishing to the
-- required higher-cohomology vanishing for every `K`.
/-- Lemma 21.14.1: for a morphism of ringed topoi, formalized here by a morphism of ringed sites
`f`, the pushforward `f_* \mathcal I` of an injective `\mathcal O_{\mathcal C}`-module sheaf
`\mathcal I` is totally acyclic on the target site. -/
theorem modulePushforward_isTotallyAcyclicOne_of_injective
    (ℐ : SheafOfModules X.structureSheaf) (hℐ : Injective ℐ) :
    IsTotallyAcyclicOne
      ((SheafOfModules.toSheaf Y.structureSheaf).obj
        ((SheafOfModules.pushforward f.structureSheafMap).obj ℐ)) := sorry

end RingedSite.Hom

/-! ### Lemma_21_14_2 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

/- Domain-style sampling for Lemma 21.14.2:
- primary domain: adjunctions, exact functors, and injective-object preservation for module sheaves
  on ringed sites;
- sampled owner declarations:
  `Functor.PreservesInjectiveObjects`,
  `CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint`,
  `Functor.injective_obj_of_injective`,
  `RingedSite.Hom.IsFlat.pullback_exact`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `RingedSite.Hom.modulePushforward`;
- best owner abstraction: `Functor.PreservesInjectiveObjects` for the canonical direct-image
  functor `f.modulePushforward`;
- primitive data: the morphism of ringed sites `f` together with the flatness instance `[f.IsFlat]`;
- derived API: the source-facing injectivity statement for the direct image of an injective module
  sheaf.

Source/core/bridge triage:
- `source-facing`: the textbook claim that flat direct image on module sheaves preserves injective
  objects;
- `core/canonical`: `Functor.PreservesInjectiveObjects`,
  `CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint`, and
  `SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap`;
- `bridge/view`: this ringed-site specialization using the canonical pullback exactness owner
  `IsFlat.pullback_exact`. -/

/-- For a flat morphism of ringed sites, direct image on module sheaves preserves injective
objects. -/
-- Proof sketch: combine the canonical adjunction `f^* ⊣ f_*` with the exactness owner
-- `IsFlat.pullback_exact`, then apply the Chapter 12 adjunction criterion
-- `CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint`.
instance modulePushforward_preservesInjectiveObjects [f.IsFlat] :
    f.modulePushforward.PreservesInjectiveObjects := by
  let v : SheafOfModules Y.structureSheaf ⥤ SheafOfModules X.structureSheaf := f^*
  let u : SheafOfModules X.structureSheaf ⥤ SheafOfModules Y.structureSheaf := f.modulePushforward
  let _ : Abelian (SheafOfModules X.structureSheaf) := inferInstance
  let _ : Abelian (SheafOfModules Y.structureSheaf) := inferInstance
  let _ : v.Additive := by
    simpa [v] using (inferInstance : (f^*).Additive)
  have adj : v ⊣ u := by
    simpa [v, u] using SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap
  have hExact : exactFunctor _ _ v := by
    simpa [v] using (IsFlat.pullback_exact : exactFunctor _ _ (f^*))
  simpa [u] using CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint adj hExact

-- Proof sketch: apply the preceding injective-preservation instance for
-- `SheafOfModules.pushforward f.structureSheafMap` to the given injective module sheaf `ℐ`.
/-- Lemma 21.14.2: if `f : (\mathit{Sh}(\mathcal C), \mathcal O_\mathcal C) \to
(\mathit{Sh}(\mathcal D), \mathcal O_\mathcal D)` is flat, formalized here by a flat morphism of
ringed sites `f`, then the direct image `f_* \mathcal I` of any injective
`\mathcal O_\mathcal C`-module `\mathcal I` is an injective `\mathcal O_\mathcal D`-module. -/
theorem modulePushforward_injective_of_isFlat
    [f.IsFlat] (ℐ : SheafOfModules X.structureSheaf) (hℐ : Injective ℐ) :
    Injective (f.modulePushforward.obj ℐ) :=
  f.modulePushforward.injective_obj_of_injective hℐ

end RingedSite.Hom

/-! ### Lemma_21_14_3 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Sheaf
open Opposite
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

/-- The functor sending an `\mathcal O`-module sheaf on a ringed topos presentation `X` to its
sections over the object `U`, viewed as an abelian-group-valued functor. -/
abbrev ringedToposModuleSectionsOverObjectFunctor
    (X : _root_.RingedSite.{u, v}) (U : X) :
    SheafOfModules X.structureSheaf ⥤ AddCommGrpCat.{v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{v} ⋙
    (CategoryTheory.evaluation Xᵒᵖ AddCommGrpCat.{v}).obj (op U)

/-- The functor sending an `\mathcal O`-module sheaf on a ringed topos presentation `X` to its
sections over a sheaf of sets `K` on the underlying topos. -/
abbrev ringedToposModuleSectionsOnSheafFunctor
    (X : _root_.RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{v}]
    [HasSheafify X.siteTopology AddCommGrpCat.{v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (K : Sheaf X.siteTopology (Type v))
    [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf (localizationTopology K) AddCommGrpCat.{v})] :
    SheafOfModules X.structureSheaf ⥤ AddCommGrpCat.{v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    localizationInverseImage K ⋙
    Sheaf.Γ (localizationTopology K) AddCommGrpCat.{v}

section

variable (X : _root_.RingedSite.{u, v})
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{v}]
variable [HasSheafify X.siteTopology AddCommGrpCat.{v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
variable [HasExt.{w} (Sheaf X.siteTopology AddCommGrpCat.{v})]

-- Proof sketch: identify the higher right-derived functors of sections over `K` with the positive
-- cohomology groups `H^p(K, (SheafOfModules.toSheaf X.structureSheaf).obj ℱ)`, and then apply the
-- defining vanishing built into `IsTotallyAcyclicOne`.
/-- Lemma 21.14.3: if the underlying abelian sheaf of an `\mathcal O`-module sheaf on a
ringed topos presentation `X` is totally acyclic, then the module sheaf is right acyclic for the
sections functor over any sheaf of sets `K` on `X`. -/
theorem totallyAcyclicModule_isRightAcyclicForSectionsOnSheaf
    (K : Sheaf X.siteTopology (Type v))
    [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf (localizationTopology K) AddCommGrpCat.{v})]
    [Functor.Additive (ringedToposModuleSectionsOnSheafFunctor X K)]
    [((mapHomotopyCategoryToDerived (ringedToposModuleSectionsOnSheafFunctor X K)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules X.structureSheaf) (up ℤ)))]
    (ℱ : SheafOfModules X.structureSheaf)
    [IsTotallyAcyclicOne ((SheafOfModules.toSheaf X.structureSheaf).obj ℱ)] :
    IsRightAcyclicForAdditiveFunctor (ringedToposModuleSectionsOnSheafFunctor X K) ℱ := sorry

-- Proof sketch: the higher right-derived functors of sections over `U` compute the groups
-- `H^p(U, (SheafOfModules.toSheaf X.structureSheaf).obj ℱ)`, so total acyclicity forces them to
-- vanish in positive degree.
/-- A totally acyclic `\mathcal O`-module sheaf on a ringed topos presentation `X` is right
acyclic for the functor `H^0(U, -)` for every object `U` of the underlying site. -/
theorem totallyAcyclicModule_isRightAcyclicForSectionsOverObject
    (U : X) (ℱ : SheafOfModules X.structureSheaf)
    [((mapHomotopyCategoryToDerived (ringedToposModuleSectionsOverObjectFunctor X U)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules X.structureSheaf) (up ℤ)))]
    [IsTotallyAcyclicOne ((SheafOfModules.toSheaf X.structureSheaf).obj ℱ)] :
    IsRightAcyclicForAdditiveFunctor (ringedToposModuleSectionsOverObjectFunctor X U) ℱ := sorry

-- Proof sketch: take `K` to be a terminal sheaf of sets on `X`; sections over such a `K`
-- identify with global sections on the underlying topos, so the previous acyclicity statement
-- specializes to `Γ(X, -)`.
/-- If `K` is a terminal sheaf of sets on the underlying topos of `X`, then a totally acyclic
`\mathcal O`-module sheaf on `X` is right acyclic for global sections. -/
theorem totallyAcyclicModule_isRightAcyclicForGlobalSections
    (K : Sheaf X.siteTopology (Type v)) (_hK : Limits.IsTerminal K)
    [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf (localizationTopology K) AddCommGrpCat.{v})]
    [Functor.Additive (ringedToposModuleSectionsOnSheafFunctor X K)]
    [((mapHomotopyCategoryToDerived (ringedToposModuleSectionsOnSheafFunctor X K)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules X.structureSheaf) (up ℤ)))]
    (ℱ : SheafOfModules X.structureSheaf)
    [IsTotallyAcyclicOne ((SheafOfModules.toSheaf X.structureSheaf).obj ℱ)] :
    IsRightAcyclicForAdditiveFunctor (ringedToposModuleSectionsOnSheafFunctor X K) ℱ := sorry

end

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [HasWeakSheafify JC AddCommGrpCat.{v}] [HasSheafify JC AddCommGrpCat.{v}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasExt.{w} (Sheaf JC AddCommGrpCat.{v})]
variable [HasSheafify JD AddCommGrpCat.{v}] [JD.WEqualsLocallyBijective AddCommGrpCat.{v}]
variable (F : D ⥤ C) [Functor.IsContinuous F JD JC]
variable {𝒪C : Sheaf JC RingCat.{v}} {𝒪D : Sheaf JD RingCat.{v}}
variable (fSharp : 𝒪D ⟶ (F.sheafPushforwardContinuous RingCat.{v} JD JC).obj 𝒪C)

-- Proof sketch: by Lemma `18.7.2`, any morphism of ringed topoi may be presented by a morphism
-- of sites, and in that setting the higher direct images are computed by sectionwise cohomology.
-- Total acyclicity kills those positive cohomology groups, so the positive right-derived
-- pushforwards vanish.
/-- In the site-presented form of a morphism of ringed topoi, a totally acyclic `\mathcal O`-module
sheaf is right acyclic for direct image. -/
theorem totallyAcyclicModule_isRightAcyclicForPushforward
    (ℱ : SheafOfModules 𝒪C)
    [IsTotallyAcyclicOne ((SheafOfModules.toSheaf 𝒪C).obj ℱ)]
    [Functor.Additive (SheafOfModules.pushforward fSharp)]
    [((mapHomotopyCategoryToDerived (SheafOfModules.pushforward fSharp)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules 𝒪C) (up ℤ)))] :
    IsRightAcyclicForAdditiveFunctor (SheafOfModules.pushforward fSharp) ℱ := sorry

end

end CategoryTheory

/-! ### Remark_21_14_4 (from Chap21) -/
open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

/-- The class of quasi-isomorphisms on cochain complexes of `\mathcal O_X`-modules. -/
abbrev ModuleQis (X : RingedSite.{u, v}) :=
  HomotopyCategory.quasiIso (SheafOfModules X.structureSheaf) (up ℤ)

/-- The direct-image functor on `\mathcal O`-modules attached to a morphism of ringed sites. -/
abbrev modulePushforward {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) :
    SheafOfModules X.structureSheaf ⥤ SheafOfModules Y.structureSheaf :=
  SheafOfModules.pushforward f.structureSheafMap

/-- The global-sections functor on `\mathcal O_X`-modules for a ringed-site presentation `X`. -/
abbrev moduleGlobalSectionsFunctor (X : RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}] :
    SheafOfModules X.structureSheaf ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    CategoryTheory.Sheaf.Γ X.siteTopology AddCommGrpCat.{max u v}

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{max u v}]
variable [Functor.Additive (modulePushforward f)]
variable [Functor.Additive (moduleGlobalSectionsFunctor Y)]
variable [Functor.HasRightDerivedFunctor
  (mapHomotopyCategoryToDerived (moduleGlobalSectionsFunctor Y))
  (ModuleQis Y)]

-- Proof sketch: by Lemma `21.14.1`, the pushforward of an injective `\mathcal O_X`-module is
-- totally acyclic on `Y`. Lemma `21.14.3` identifies total acyclicity with right acyclicity for
-- global sections, so every injective is sent by `f_*` to a `Γ(Y,-)`-acyclic object. This is
-- exactly the hypothesis needed to apply Derived Categories, Lemma `13.22.1` and deduce the
-- comparison `RΓ(Y, Rf_* \mathcal F) ≅ RΓ(X, \mathcal F)`.
/-- Remark 21.14.4: for a morphism of ringed topoi, formalized here by a morphism of ringed sites
`f`, the pushforward of any injective `\mathcal O_\mathcal C`-module sheaf is right acyclic for
global sections on the target. Consequently the Leray-type comparison
`RΓ(\mathcal D, Rf_* \mathcal F) = RΓ(\mathcal C, \mathcal F)` is available by Derived
Categories, Lemma `13.22.1`. -/
theorem modulePushforward_injective_isRightAcyclicForGlobalSections
    (ℐ : SheafOfModules X.structureSheaf) (hℐ : Injective ℐ) :
    IsRightAcyclicForAdditiveFunctor (moduleGlobalSectionsFunctor Y)
      ((modulePushforward f).obj ℐ) := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_14_5_Leray_spectral_sequence (from Chap21) -/
open CategoryTheory
open DerivedCategory.TStructure
open CategoryTheory.Limits

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

/-- The abelian category of sheaves of modules on the ringed site `X`. -/
abbrev ModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The bounded-below derived category `D^+(\mathcal O_X)` of module sheaves on `X`. -/
abbrev ModuleDerivedPlus (X : RingedSite.{u, v}) :=
  CategoryTheory.boundedBelowDerivedCategory (ModuleCat X)

/-- The direct-image functor on module sheaves attached to a morphism of ringed sites. -/
abbrev modulePushforward {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) :
    ModuleCat X ⥤ ModuleCat Y :=
  SheafOfModules.pushforward f.structureSheafMap

/-- The global-sections functor on `\mathcal O_X`-modules, computed on the underlying abelian
sheaf. -/
abbrev moduleGlobalSectionsFunctor (X : RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}] :
    ModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    Sheaf.Γ X.siteTopology AddCommGrpCat.{max u v}

/-- The `q`-th cohomology module sheaf of a bounded-below derived `\mathcal O_X`-complex. -/
abbrev moduleDerivedCohomology (X : RingedSite.{u, v})
    (K : ModuleDerivedPlus X) (q : ℤ) :
    ModuleCat X :=
  (((ObjectProperty.ι
      (t.plus : ObjectProperty (DerivedCategory (ModuleCat X)))) ⋙
        DerivedCategory.homologyFunctor (ModuleCat X) q).obj K)

local instance (X : RingedSite.{u, v}) :
    CategoryTheory.Functor.IsLocalization
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (ModuleCat X))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (ModuleCat X)) :=
  CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization (ModuleCat X)

/-- The bounded-below right derived direct-image functor on module sheaves. -/
abbrev modulePushforwardDerivedPlus
    {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [EnoughInjectives (ModuleCat X)]
    [f.modulePushforward.Additive]
    [CategoryTheory.AdditiveFunctorDerivedLocalizationSituation f.modulePushforward] :
    ModuleDerivedPlus X ⥤ ModuleDerivedPlus Y :=
  CategoryTheory.Functor.totalRightDerived
    (CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow f.modulePushforward)
    (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (ModuleCat X))
    (CategoryTheory.boundedBelowHomotopyQuasiIso (ModuleCat X))

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{max u v}]
variable [EnoughInjectives (ModuleCat X)]
variable [EnoughInjectives (ModuleCat Y)]
variable [f.modulePushforward.Additive]
variable [(moduleGlobalSectionsFunctor X).Additive]
variable [(moduleGlobalSectionsFunctor Y).Additive]
variable [CategoryTheory.AdditiveFunctorDerivedLocalizationSituation f.modulePushforward]
variable [CategoryTheory.AdditiveFunctorDerivedLocalizationSituation
  (moduleGlobalSectionsFunctor X)]
variable [CategoryTheory.AdditiveFunctorDerivedLocalizationSituation
  (moduleGlobalSectionsFunctor Y)]

/-- The `E_2^{p,q}` term `H^p(\mathcal D, R^q f_*(K))` of the Leray spectral sequence attached
to a bounded-below derived `\mathcal O_{\mathcal C}`-complex `K`. -/
abbrev leraySpectralSequencePageTwoTerm
    (K : ModuleDerivedPlus X) (p : ℕ) (q : ℤ) :
    AddCommGrpCat.{max u v} :=
  ((moduleGlobalSectionsFunctor Y).rightDerived p).obj
    (moduleDerivedCohomology Y
      ((modulePushforwardDerivedPlus f).obj K) q)

/-- The abutment `H^n(\mathcal C, K)` of the Leray spectral sequence, computed as the `n`-th
cohomology of the bounded-below derived global sections of `K`. -/
abbrev leraySpectralSequenceAbutment
    (K : ModuleDerivedPlus X) (n : ℤ) :
    AddCommGrpCat.{max u v} :=
  (((ObjectProperty.ι
      (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{max u v}))) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} n).obj
      ((CategoryTheory.Functor.totalRightDerived
          (CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
            (moduleGlobalSectionsFunctor X))
          (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (ModuleCat X))
          (CategoryTheory.boundedBelowHomotopyQuasiIso (ModuleCat X))).obj K))

/-- A cohomological spectral sequence realizing the Leray spectral sequence for a morphism of
ringed topoi presented by a morphism of ringed sites `f` and a bounded-below derived
`\mathcal O_{\mathcal C}`-complex `K`. -/
structure LeraySpectralSequence
    (K : ModuleDerivedPlus X) where
  /-- The chosen cohomological spectral sequence. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat.{max u v} 0
  /-- The `E_2`-page identifies with `H^p(\mathcal D, R^q f_*(K))`. -/
  pageTwoIso :
    ∀ p : ℕ, ∀ q : ℤ,
      (spectralSequence.page 2).X (Int.ofNat p, q) ≅
        leraySpectralSequencePageTwoTerm f K p q
  /-- The Leray spectral sequence is bounded. -/
  bounded : CohomologicalSpectralSequence.IsBounded spectralSequence
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : ℤ → AddCommGrpCat.{max u v}
  /-- The abutment identifies with the hypercohomology `H^n(\mathcal C, K)`. -/
  targetIso :
    ∀ n : ℤ,
      abutment n ≅ leraySpectralSequenceAbutment K n

-- Proof sketch: apply the Grothendieck spectral sequence to the composite
-- `Γ(\mathcal C, -) = Γ(\mathcal D, -) ∘ f_*` on sheaves of `\mathcal O`-modules. Lemma
-- `21.14.1` shows that the pushforward of an injective module sheaf is totally acyclic on the
-- target, and Lemma `21.14.3` upgrades total acyclicity to right acyclicity for global sections.
-- Therefore the hypotheses of Lemma `13.22.2` hold for the pair
-- `f_* : Mod(\mathcal O_{\mathcal C}) ⥤ Mod(\mathcal O_{\mathcal D})` and
-- `Γ(\mathcal D, -)`, yielding the stated `E₂`-page and abutment.
/-- Lemma 21.14.5 (Leray spectral sequence): for a morphism of ringed topoi, formalized here by a
morphism of ringed sites `f`, and a bounded-below complex `K` of `\mathcal O_{\mathcal C}`-modules,
there is a cohomological spectral sequence whose `E_2^{p,q}`-term is
`H^p(\mathcal D, R^q f_*(K))` and whose abutment is `H^{p+q}(\mathcal C, K)`. -/
theorem exists_leraySpectralSequence
    (K : ModuleDerivedPlus X) :
    Nonempty (LeraySpectralSequence f K) := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_14_6 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 21.14.6:
- primary domain: the Leray spectral sequence for global cohomology of sheaves of modules on a
  morphism of ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.modulePushforward`,
  `RingedSite.Hom.higherDirectImageModule`,
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`,
  `RingedSite.Hom.exists_leraySpectralSequence`;
- best owner abstraction:
  the source-facing statements here are the two Leray degeneration consequences, while the
  owner-level module direct-image data should come from `f.modulePushforward` and
  `higherDirectImageModule f ℱ q`, not from new local wrappers;
- primitive data:
  a morphism `f : X ⟶ Y`, a module sheaf `ℱ : SheafOfModules X.structureSheaf`, and vanishing
  hypotheses on `R^q f_* ℱ` or on its positive-degree cohomology on `Y`;
- derived API:
  the underlying-abelian-sheaf global cohomology object
  `AddCommGrpCat.of (((SheafOfModules.toSheaf X.structureSheaf).obj ℱ).H p)`.

Source/core/bridge triage:
- `source-facing`: the two cohomological comparison theorems below;
- `core/canonical`: `f.modulePushforward` and `higherDirectImageModule f ℱ q`;
- `bridge/view`: the underlying-abelian-sheaf realization of module cohomology already used in
  Chapter `21`.

The former local `moduleGlobalCohomology` abbreviation duplicated that derived view without
introducing new mathematics, so the refined file removes it and writes the canonical object
directly in the public statements. -/

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [Functor.Additive f.modulePushforward]
variable [HasInjectiveResolutions (SheafOfModules X.structureSheaf)]
variable [HasSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat.{max u v})]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat.{max u v})]

-- Proof sketch: apply the Leray spectral sequence for `f` and `ℱ`. If every higher direct image
-- `R^q f_* ℱ` with `q > 0` vanishes, the `E₂`-page is concentrated on the `q = 0` row, so the
-- abutment identifies with the degree-`p` cohomology of `f_* ℱ` on the target site.
/-- Lemma 21.14.6 (1): if the higher direct images `R^q f_* \mathcal F` vanish for `q > 0`,
then the global degree-`p` cohomology of `\mathcal F` on `(\mathcal C, \mathcal O_\mathcal C)`
is canonically isomorphic to the global degree-`p` cohomology of `f_* \mathcal F` on
`(\mathcal D, \mathcal O_\mathcal D)`. -/
theorem moduleGlobalCohomology_iso_pushforward_of_higherDirectImageModule_isZero
    (ℱ : SheafOfModules X.structureSheaf)
    (hRq : ∀ q : ℕ, 0 < q → IsZero (higherDirectImageModule f ℱ q))
    (p : ℕ) :
    IsIsomorphic
      (AddCommGrpCat.of (((SheafOfModules.toSheaf X.structureSheaf).obj ℱ).H p))
      (AddCommGrpCat.of (((SheafOfModules.toSheaf Y.structureSheaf).obj
        (f.modulePushforward.obj ℱ)).H p)) := sorry

-- Proof sketch: apply the Leray spectral sequence for `f` and `ℱ`. If every positive-degree
-- cohomology group of every higher direct image `R^q f_* ℱ` vanishes on the target site, the
-- `E₂`-page is concentrated in the `p = 0` column, so the abutment in total degree `q`
-- identifies with the edge term `H^0(\mathcal D, R^q f_* \mathcal F)`.
/-- Lemma 21.14.6 (2): if `H^p(\mathcal D, R^q f_* \mathcal F) = 0` for all `q` and all `p > 0`,
then the global degree-`q` cohomology of `\mathcal F` on
`(\mathcal C, \mathcal O_\mathcal C)` is canonically isomorphic to the degree-`0` cohomology of
`R^q f_* \mathcal F` on `(\mathcal D, \mathcal O_\mathcal D)`. -/
theorem moduleGlobalCohomology_iso_degreeZero_higherDirectImageModule_of_acyclicity
    (ℱ : SheafOfModules X.structureSheaf)
    (hHp : ∀ q p : ℕ, 0 < p →
      IsZero (AddCommGrpCat.of (((SheafOfModules.toSheaf Y.structureSheaf).obj
        (higherDirectImageModule f ℱ q)).H p)))
    (q : ℕ) :
    IsIsomorphic
      (AddCommGrpCat.of (((SheafOfModules.toSheaf X.structureSheaf).obj ℱ).H q))
      (AddCommGrpCat.of (((SheafOfModules.toSheaf Y.structureSheaf).obj
        (higherDirectImageModule f ℱ q)).H 0)) := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_14_7_Relative_Leray_spectral_sequence (from Chap21) -/
open CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe w u v

namespace RingedSite.Hom

variable {X Y Z : RingedSite.{u, v}}

local instance (X : RingedSite.{u, v}) :
    CategoryTheory.Functor.IsLocalization
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (ModuleCat X))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (ModuleCat X)) :=
  CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization (ModuleCat X)

/-- The abelian category of sheaves of modules on the ringed site `X`. -/
abbrev ModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The bounded-below derived category `D^+(\mathcal O_X)` of module sheaves on `X`. -/
abbrev ModuleDerivedPlus (X : RingedSite.{u, v})
    [HasDerivedCategory.{w} (ModuleCat X)] :=
  CategoryTheory.boundedBelowDerivedCategory (ModuleCat X)

/-- The bounded-below right derived direct-image functor on module sheaves. -/
abbrev modulePushforwardDerivedPlus {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [HasDerivedCategory.{w} (ModuleCat X)]
    [HasDerivedCategory.{w} (ModuleCat Y)]
    [EnoughInjectives (ModuleCat X)]
    [Functor.Additive (modulePushforward f)]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)] :
    ModuleDerivedPlus X ⥤ ModuleDerivedPlus Y :=
  CategoryTheory.Functor.totalRightDerived
    (CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow f.modulePushforward)
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (ModuleCat X))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (ModuleCat X))

/-- The degree-`q` cohomology sheaf of the bounded-below derived direct image `Rf_* K`. -/
abbrev modulePushforwardDerivedPlusCohomology
    (f : RingedSite.Hom X Y)
    [HasDerivedCategory.{w} (ModuleCat X)]
    [HasDerivedCategory.{w} (ModuleCat Y)]
    [EnoughInjectives (ModuleCat X)]
    [Functor.Additive (modulePushforward f)]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)]
    (K : ModuleDerivedPlus X) (q : ℕ) :
    ModuleCat Y :=
  (((ObjectProperty.ι (t.plus : ObjectProperty (DerivedCategory (ModuleCat Y)))) ⋙
      DerivedCategory.homologyFunctor (ModuleCat Y) q).obj
    ((modulePushforwardDerivedPlus f).obj K))

/-- The degree-`n` cohomology sheaf of the bounded-below derived direct image
`R(g \circ f)_* K`. -/
abbrev moduleCompositePushforwardDerivedPlusCohomology
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
    [HasDerivedCategory.{w} (ModuleCat X)]
    [HasDerivedCategory.{w} (ModuleCat Z)]
    [EnoughInjectives (ModuleCat X)]
    [Functor.Additive (modulePushforward (RingedSite.Hom.comp f g))]
    [AdditiveFunctorDerivedLocalizationSituation
      (modulePushforward (RingedSite.Hom.comp f g))]
    (K : ModuleDerivedPlus X) (n : ℕ) :
    ModuleCat Z :=
  (((ObjectProperty.ι (t.plus : ObjectProperty (DerivedCategory (ModuleCat Z)))) ⋙
      DerivedCategory.homologyFunctor (ModuleCat Z) n).obj
    ((modulePushforwardDerivedPlus (RingedSite.Hom.comp f g)).obj K))

/-- A functorial package for the relative Leray spectral sequence attached to a composable pair of
morphisms of ringed topoi, formalized here by ringed-site morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`.
-/
structure RelativeLeraySpectralSequence
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
    [HasInjectiveResolutions (ModuleCat X)]
    [HasInjectiveResolutions (ModuleCat Y)]
    [Functor.Additive (modulePushforward f)]
    [Functor.Additive (modulePushforward g)]
    [Functor.Additive (modulePushforward (RingedSite.Hom.comp f g))] where
  /-- The cohomological spectral sequence attached to each `\mathcal O_X`-module, functorially in
  the module and starting on the `E₂`-page. -/
  spectralSequenceFunctor :
    ModuleCat X ⥤ E₂CohomologicalSpectralSequenceNat (ModuleCat Z)
  /-- The `E₂`-page identifies with the iterated higher direct images
  `R^p g_* (R^q f_* \mathcal F)`. -/
  pageTwoIso :
    ∀ (ℱ : ModuleCat X) (p q : ℕ),
      ((spectralSequenceFunctor.obj ℱ).page 2).X (p, q) ≅
        higherDirectImageModule g (higherDirectImageModule f ℱ q) p
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : ModuleCat X → ℕ → ModuleCat Z
  /-- The abutment identifies with the higher direct images of the composite morphism
  `(g \circ f)_*`. -/
  targetIso :
    ∀ (ℱ : ModuleCat X) (n : ℕ),
      abutment ℱ n ≅ higherDirectImageModule (RingedSite.Hom.comp f g) ℱ n

/-- A bounded-below-complex version of the relative Leray spectral sequence attached to a
composable pair of morphisms of ringed topoi, formalized here by ringed-site morphisms
`f : X ⟶ Y` and `g : Y ⟶ Z`. -/
structure RelativeLeraySpectralSequenceBoundedBelow
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
    [HasDerivedCategory.{w} (ModuleCat X)]
    [HasDerivedCategory.{w} (ModuleCat Y)]
    [HasDerivedCategory.{w} (ModuleCat Z)]
    [EnoughInjectives (ModuleCat X)]
    [HasInjectiveResolutions (ModuleCat Y)]
    [Functor.Additive (modulePushforward f)]
    [Functor.Additive (modulePushforward g)]
    [Functor.Additive (modulePushforward (RingedSite.Hom.comp f g))]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)]
    [AdditiveFunctorDerivedLocalizationSituation
      (modulePushforward (RingedSite.Hom.comp f g))]
    (K : ModuleDerivedPlus X) where
  /-- The cohomological spectral sequence attached to the bounded-below complex `K`, starting on
  the `E₂`-page. -/
  spectralSequence : E₂CohomologicalSpectralSequenceNat (ModuleCat Z)
  /-- The `E₂`-page identifies with the iterated higher direct images
  `R^p g_* (H^q(Rf_* K))`. -/
  pageTwoIso :
    ∀ p q : ℕ,
      (spectralSequence.page 2).X (p, q) ≅
        higherDirectImageModule g (modulePushforwardDerivedPlusCohomology f K q) p
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : ℕ → ModuleCat Z
  /-- The abutment identifies with the cohomology sheaves of `R(g \circ f)_* K`. -/
  targetIso :
    ∀ n : ℕ,
      abutment n ≅ moduleCompositePushforwardDerivedPlusCohomology f g K n

-- Proof sketch: apply the Grothendieck spectral sequence to the composite
-- `SheafOfModules.pushforward f.structureSheafMap ⋙ SheafOfModules.pushforward g.structureSheafMap`.
-- Lemma `21.14.1` shows that the pushforward of an injective module sheaf is totally acyclic on
-- the intermediate ringed topos, and Lemma `21.14.3` upgrades total acyclicity to right
-- acyclicity for the second pushforward. The Chapter `13` Grothendieck spectral sequence then
-- produces the desired `E₂`-page and abutment, while naturality of the construction gives
-- functoriality in `\mathcal F`.
/-- Lemma 21.14.7 (Relative Leray spectral sequence): for composable morphisms of ringed topoi,
formalized here by ringed-site morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, there is a cohomological
spectral sequence functorial in an `\mathcal O_X`-module `\mathcal F` whose
`E_2^{p,q}`-term is `R^p g_* (R^q f_* \mathcal F)` and whose abutment is
`R^{p + q} (g \circ f)_* \mathcal F`. -/
theorem exists_relativeLeraySpectralSequence
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
    [HasInjectiveResolutions (ModuleCat X)]
    [HasInjectiveResolutions (ModuleCat Y)]
    [Functor.Additive (modulePushforward f)]
    [Functor.Additive (modulePushforward g)]
    [Functor.Additive (modulePushforward (RingedSite.Hom.comp f g))] :
    Nonempty (RelativeLeraySpectralSequence f g) := sorry

-- Proof sketch: apply Lemma `13.22.2` directly to the bounded-below derived categories of module
-- sheaves and to the composable direct-image functors `f_*` and `g_*`. The acyclicity input comes
-- from the module-sheaf form of the Leray acyclicity lemmas `21.14.1` and `21.14.3`, now used on
-- representatives of bounded-below complexes.
/-- The bounded-below derived version of the relative Leray spectral sequence for module sheaves on
ringed sites. -/
theorem exists_relativeLeraySpectralSequence_boundedBelow
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
    [HasDerivedCategory.{w} (ModuleCat X)]
    [HasDerivedCategory.{w} (ModuleCat Y)]
    [HasDerivedCategory.{w} (ModuleCat Z)]
    [EnoughInjectives (ModuleCat X)]
    [HasInjectiveResolutions (ModuleCat Y)]
    [Functor.Additive (modulePushforward f)]
    [Functor.Additive (modulePushforward g)]
    [Functor.Additive (modulePushforward (RingedSite.Hom.comp f g))]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)]
    [AdditiveFunctorDerivedLocalizationSituation
      (modulePushforward (RingedSite.Hom.comp f g))]
    (K : ModuleDerivedPlus X) :
    Nonempty (RelativeLeraySpectralSequenceBoundedBelow f g K) := sorry

end RingedSite.Hom
