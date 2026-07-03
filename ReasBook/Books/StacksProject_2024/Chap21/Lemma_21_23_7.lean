import Mathlib
import StacksProject_2024.Chap13.Remark_13_34_5
import StacksProject_2024.Chap18.Definition_18_6_1
import StacksProject_2024.Chap19.Lemma_19_13_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over a fixed object
`U` of the ringed site `X`, viewed on underlying abelian groups. -/
private abbrev ringedSiteSectionsOverObjectFunctor (X : RingedSite.{u, v}) (U : X) :
    RingedSiteModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

-- Proof sketch: `SheafOfModules.toSheaf`, `sheafToPresheaf`, and evaluation at `U` are additive,
-- so their composite sections functor is additive as well.
/-- The sections functor over a fixed object of a ringed site is additive. -/
private theorem ringedSiteSectionsOverObjectFunctor_isAdditive
    (X : RingedSite.{u, v}) (U : X)
    [hAb : Abelian (RingedSiteModuleCat X)] :
    @Functor.Additive
      (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteSectionsOverObjectFunctor X U) := sorry

/-- The right derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in derived
abelian groups. -/
private abbrev ringedSiteDerivedSectionsOverObjectFunctor
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)] :
    DerivedCategory (RingedSiteModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
    _ _ _ _
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

/-- The degree-`p` cohomology group `H^p(U, \mathcal F)` of a module sheaf on a ringed site,
computed by applying derived sections over `U` to `\mathcal F[0]`. -/
private abbrev ringedSiteModuleCohomologyOverObject
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (p : ℤ) (ℱ : RingedSiteModuleCat X) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} p).obj
    ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj
      ((DerivedCategory.singleFunctor (RingedSiteModuleCat X) (0 : ℤ)).obj ℱ))

/-- Witness data for the eventual local vanishing hypothesis on the cohomology sheaves of a
derived object over a fixed basis object `V`. -/
private structure BasiswiseEventualCohomologySheafVanishingData
    (X : RingedSite.{u, v})
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (E : DerivedCategory (RingedSiteModuleCat X))
    (V : X) where
  /-- A degree bound for the local vanishing condition over `V`. -/
  pBound : ℤ → ℤ
  /-- A cofinal family of coverings of `V`. -/
  CovV : X.siteTopology.Cover V → Prop
  /-- The chosen family of coverings is cofinal in all coverings of `V`. -/
  cofinal :
    ∀ S : X.siteTopology.Cover V,
      ∃ T : X.siteTopology.Cover V, CovV T ∧ Nonempty (T ⟶ S)
  /-- On each covering in the cofinal family, sufficiently high cohomology of the cohomology
  sheaves of `E` vanishes on every member. -/
  vanishing :
    ∀ ⦃T : X.siteTopology.Cover V⦄, CovV T → ∀ I : T.Arrow, ∀ p m : ℤ,
      pBound m < p →
        IsZero
          (ringedSiteModuleCohomologyOverObject X I.Y p
            ((DerivedCategory.homologyFunctor (RingedSiteModuleCat X) (m - p)).obj E))

-- Proof sketch: for each `V ∈ B`, apply the stated vanishing bounds on the cover system `CovV`
-- to the cohomology sheaves `H^{m-p}(E)`, use the truncation triangles from Remark `13.12.4` to
-- obtain eventual isomorphisms on the towers `H^{m-1}(V_i, \tau_{\ge -n} E)` and
-- `H^m(V_i, \tau_{\ge -n} E)`, deduce eventual injectivity from Lemma `21.23.6`, and then apply
-- the comparison-independence criterion of Remark `13.34.5`.
/-- Lemma 21.23.7: let `(\mathcal C, \mathcal O)` be a ringed site, let
`E ∈ D(\mathcal O)`, and let `B` be a subset of objects of `\mathcal C`. Assume every object of
`\mathcal C` has a covering by members of `B`, and for each `V ∈ B` there are a bound
`pBound(V,-) : \mathbf Z \to \mathbf Z` and a cofinal system `Cov_V` of coverings of `V` such
that `H^p(V_i, H^{m-p}(E)) = 0` for every member `V_i` of every covering in `Cov_V` whenever
`p > pBound(V,m)`. Then any compatible map from `E` to a chosen derived limit of the truncation
tower `(\tau_{\ge -n} E)_n`, formalizing the canonical map
`E \to R\!\varprojlim_n \tau_{\ge -n} E`, is an isomorphism in `D(\mathcal O)`. -/
theorem truncationComparison_isIso_of_basiswise_eventual_cohomologySheaf_vanishing
    (X : RingedSite.{u, v})
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (E K : DerivedCategory (RingedSiteModuleCat X))
    (c : E ⟶ K)
    (hc : CategoryTheory.IsTruncationDerivedLimitComparison E K c)
    (B : Set X)
    (hcover :
      ∀ U : X, ∃ S : X.siteTopology.Cover U, ∀ I : S.Arrow, I.Y ∈ B)
    (hvanish :
      ∀ ⦃V : X⦄, V ∈ B →
        BasiswiseEventualCohomologySheafVanishingData X E V) :
    IsIso c := sorry
