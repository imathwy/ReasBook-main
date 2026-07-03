import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_15_1 (from Chap21) -/
open CategoryTheory

noncomputable section

universe w u v

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

section

variable {X' X Y' Y : RingedSite.{u, v}}
variable (g' : RingedSite.Hom X' X) (f' : RingedSite.Hom X' Y')
variable (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)

variable [Functor.IsCocontinuous f.base Y.siteTopology X.siteTopology]
variable [Functor.IsCocontinuous f'.base Y'.siteTopology X'.siteTopology]
variable [Functor.IsCocontinuous g.base Y.siteTopology Y'.siteTopology]
variable [Functor.IsCocontinuous g'.base X.siteTopology X'.siteTopology]

variable [EnoughInjectives (ModuleCat X)]
variable [EnoughInjectives (ModuleCat X')]
variable [EnoughInjectives (ModuleCat Y)]
variable [EnoughInjectives (ModuleCat Y')]

variable [f.modulePushforward.Additive]
variable [f'.modulePushforward.Additive]
variable [g.modulePullback.Additive]
variable [g'.modulePullback.Additive]

variable [CategoryTheory.AdditiveFunctorDerivedLocalizationSituation f.modulePushforward]
variable [CategoryTheory.AdditiveFunctorDerivedLocalizationSituation f'.modulePushforward]
variable [CategoryTheory.AdditiveFunctorDerivedLocalizationSituation g.modulePullback]
variable [CategoryTheory.AdditiveFunctorDerivedLocalizationSituation g'.modulePullback]

local instance (X : RingedSite.{u, v}) :
    CategoryTheory.Functor.IsLocalization
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (ModuleCat X))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (ModuleCat X)) :=
  CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization (ModuleCat X)

/-- The bounded-below right derived direct-image functor on module sheaves. -/
abbrev modulePushforwardDerivedPlus (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [CategoryTheory.AdditiveFunctorDerivedLocalizationSituation f.modulePushforward] :
    ModuleDerivedPlus X ⥤ ModuleDerivedPlus Y :=
  CategoryTheory.Functor.totalRightDerived
    (CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow f.modulePushforward)
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (ModuleCat X))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (ModuleCat X))

/-- The bounded-below right derived inverse-image functor on module sheaves. -/
abbrev modulePullbackDerivedPlus (g : RingedSite.Hom Y' Y)
    [g.modulePullback.Additive]
    [CategoryTheory.AdditiveFunctorDerivedLocalizationSituation g.modulePullback] :
    ModuleDerivedPlus Y ⥤ ModuleDerivedPlus Y' :=
  CategoryTheory.Functor.totalRightDerived
    (CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow g.modulePullback)
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (ModuleCat Y))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (ModuleCat Y))

-- Proof sketch: first apply Lemma `18.41.3 (1)` to the commutative square of ringed sites to
-- identify the underived composites `(g')^* ⋙ (f')_*` and `f_* ⋙ g^*` on module categories.
-- Then pass to the bounded-below derived functors from Chapter `13`. Under the flatness
-- hypotheses, the pullback functors are exact, so their bounded-below right derived functors
-- represent the pullbacks on `D^+`, yielding the claimed base-change morphism.
/-- Lemma 21.15.1: for a commutative square of ringed topoi presented here by ringed-site
morphisms
`\xymatrix{
(\operatorname{Sh}(\mathcal C'), \mathcal O_{\mathcal C'}) \ar[r]^{g'} \ar[d]_{f'} &
(\operatorname{Sh}(\mathcal C), \mathcal O_{\mathcal C}) \ar[d]^{f} \\
(\operatorname{Sh}(\mathcal D'), \mathcal O_{\mathcal D'}) \ar[r]_{g} &
(\operatorname{Sh}(\mathcal D), \mathcal O_{\mathcal D})
}`
with `g` and `g'` flat, every bounded-below object `\mathcal F^\bullet` of
`D^+(\mathcal O_{\mathcal C})` admits a base-change morphism
`g^* Rf_* \mathcal F^\bullet \to R(f')_* (g')^* \mathcal F^\bullet`
in `D^+(\mathcal O_{\mathcal D'})`. -/
theorem exists_boundedBelow_baseChangeMap
    (hcomm : g.base ⋙ f'.base = f.base ⋙ g'.base)
    (hcofinal : ∀ V : X,
      Functor.Final
        (CostructuredArrow.map₂ (eqToHom hcomm) (𝟙 (g'.base.obj V))))
    (hO_g :
      Y.structureSheaf =
        (g.base.sheafPushforwardContinuous RingCat.{max u v}
          Y.siteTopology Y'.siteTopology).obj Y'.structureSheaf)
    (hO_g' :
      X.structureSheaf =
        (g'.base.sheafPushforwardContinuous RingCat.{max u v}
          X.siteTopology X'.siteTopology).obj X'.structureSheaf)
    (hg : g.structureSheafMap = eqToHom hO_g)
    (hg' : g'.structureSheafMap = eqToHom hO_g')
    [g.IsFlat] [g'.IsFlat]
    (ℱ : ModuleDerivedPlus X) :
    ∃ η :
      ((modulePullbackDerivedPlus g).obj
          ((modulePushforwardDerivedPlus f).obj ℱ)) ⟶
        ((modulePushforwardDerivedPlus f').obj
          ((modulePullbackDerivedPlus g').obj ℱ)),
      True := sorry

end

end RingedSite.Hom
