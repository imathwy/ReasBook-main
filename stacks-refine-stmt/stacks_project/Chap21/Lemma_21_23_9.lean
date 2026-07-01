import Mathlib
import stacks_project.Chap13.Remark_13_34_5
import stacks_project.Chap18.Definition_18_6_1
import stacks_project.Chap19.Lemma_19_13_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable (X : RingedSite.{u, v})

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
abbrev RingedSiteModuleCat :=
  SheafOfModules X.structureSheaf

local notation "ModX" => RingedSiteModuleCat X

variable [Abelian (RingedSiteModuleCat X)]
variable [CategoryWithHomology (RingedSiteModuleCat X)]
variable [IsGrothendieckAbelian (RingedSiteModuleCat X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over a fixed object
`U` of the ringed site `X`. -/
abbrev ringedSiteSectionsOverObjectFunctor (U : X) :
    RingedSiteModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

-- Proof sketch: `SheafOfModules.toSheaf`, `sheafToPresheaf`, and evaluation at `U` are additive,
-- so their composite sections functor is additive as well.
/-- The sections functor over a fixed object of a ringed site is additive. -/
theorem ringedSiteSectionsOverObjectFunctor_isAdditive
    (U : X)
    [hAb : Abelian (RingedSiteModuleCat X)] :
    @Functor.Additive
      (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteSectionsOverObjectFunctor X U) := sorry

/-- The right derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`. -/
abbrev ringedSiteDerivedSectionsOverObjectFunctor
    (U : X)
    [hAb : Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)] :
    DerivedCategory (RingedSiteModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
    _ hAb _ AddCommGrpCat.instAbelian
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

/-- The degree-`p` objectwise cohomology group `H^p(U, K)` of a derived `\mathcal O_X`-module
`K`. -/
abbrev ringedSiteDerivedObjectwiseCohomology
    (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (p : ℤ) (K : DerivedCategory (RingedSiteModuleCat X)) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} p).obj
    ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj K)

/-- A sheaf of `\mathcal O_X`-modules viewed as a derived object concentrated in degree `0`. -/
abbrev ringedSiteSingleFunctorZero
    [Abelian (RingedSiteModuleCat X)] :
    RingedSiteModuleCat X ⥤ DerivedCategory (RingedSiteModuleCat X) :=
  DerivedCategory.singleFunctor (RingedSiteModuleCat X) (0 : ℤ)

/-- The degree-`p` cohomology group `H^p(U, \mathcal F)` of a sheaf of `\mathcal O_X`-modules,
viewed via the derived-category embedding in degree `0`. -/
abbrev ringedSiteModuleObjectwiseCohomology
    (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (p : ℤ) (ℱ : RingedSiteModuleCat X) :
    AddCommGrpCat.{max u v} :=
  ringedSiteDerivedObjectwiseCohomology X U p
    ((ringedSiteSingleFunctorZero X).obj ℱ)

-- Proof sketch: this is the uniform-basis specialization of Lemma `21.23.7`. For each basis
-- object `V ∈ B`, use the constant bound family `pBound(V, m) := pBound m` and let `Cov_V` be
-- the coverings of `V` whose members all lie in `B`; the covering hypothesis makes this family
-- cofinal, so Lemma `21.23.7` applies to the cohomology sheaves `H^{m-p}(E)` and yields that any
-- compatible truncation-derived-limit comparison `c : E ⟶ K` is an isomorphism.
/-- Lemma 21.23.9: let `(\mathcal C, \mathcal O)` be a ringed site, let `E ∈ D(\mathcal O)`,
and assume there are a function `pBound : \mathbf Z \to \mathbf Z` and a subset `B` of objects of
`\mathcal C` such that every object admits a covering by members of `B` and
`H^p(V, H^{m-p}(E)) = 0` for every `V ∈ B` whenever `p > pBound(m)`. Then any compatible map
from `E` to a chosen derived limit of the truncation tower `(\tau_{\ge -n} E)_n`, i.e. any
formalization of the canonical map `E \to R\!\varprojlim_n \tau_{\ge -n} E` from
Remark `13.34.5`, is an isomorphism in `D(\mathcal O)`. -/
theorem truncationComparison_isIso_of_uniform_basiswise_eventual_cohomologySheaf_vanishing
    (E K : DerivedCategory ModX)
    (c : E ⟶ K)
    (hc : IsTruncationDerivedLimitComparison E K c)
    (pBound : ℤ → ℤ)
    (B : Set X)
    (hcover :
      ∀ U : X, ∃ S : X.siteTopology.Cover U, ∀ I : S.Arrow, I.Y ∈ B)
    (hvanish :
      ∀ ⦃V : X⦄, V ∈ B → ∀ p m : ℤ, pBound m < p →
        IsZero
          (ringedSiteModuleObjectwiseCohomology X V p
            ((DerivedCategory.homologyFunctor ModX (m - p)).obj E))) :
    IsIso c := sorry

end
