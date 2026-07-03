import Mathlib
import StacksProject_2024.Chap13.Remark_13_34_5
import StacksProject_2024.Chap18.Definition_18_6_1
import StacksProject_2024.Chap19.Lemma_19_13_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

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
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (Opposite.op U)

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
private abbrev ringedSiteModuleObjectwiseCohomology
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

/-- Witness data for the negative-cohomology local vanishing hypothesis over a fixed basis object
`V`. -/
private structure BasiswiseNegativeCohomologySheafVanishingData
    (X : RingedSite.{u, v})
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (E : DerivedCategory (RingedSiteModuleCat X))
    (V : X) where
  /-- A nonnegative cohomological bound for the local vanishing condition over `V`. -/
  dV : ℤ
  /-- The chosen bound is nonnegative. -/
  nonneg : 0 ≤ dV
  /-- A cofinal family of coverings of `V`. -/
  CovV : X.siteTopology.Cover V → Prop
  /-- The chosen family of coverings is cofinal in all coverings of `V`. -/
  cofinal :
    ∀ S : X.siteTopology.Cover V,
      ∃ T : X.siteTopology.Cover V, CovV T ∧ Nonempty (T ⟶ S)
  /-- On each covering in the cofinal family, the negative cohomology sheaves of `E` have no
  cohomology above the bound `dV` on any member of the covering. -/
  vanishing :
    ∀ ⦃T : X.siteTopology.Cover V⦄, CovV T → ∀ I : T.Arrow, ∀ p q : ℤ,
      dV < p → q < 0 →
        IsZero
          (ringedSiteModuleObjectwiseCohomology X I.Y p
            ((DerivedCategory.homologyFunctor (RingedSiteModuleCat X) q).obj E))

-- Proof sketch: apply Lemma `21.23.7` with the bound function
-- `pBound(V, m) = d_V + max 0 m`. If `p > d_V + max 0 m`, then either `m < 0`, in which case
-- `m - p < 0`, or `m ≥ 0`, in which case `d_V < p`, hence the given vanishing hypothesis for the
-- negative cohomology sheaves of `E` yields the basiswise eventual vanishing required there.
/-- Lemma 21.23.8: let `(\mathcal C,\mathcal O)` be a ringed site, let `E ∈ D(\mathcal O)`, and
let `\mathcal B` be a subset of objects of `\mathcal C`. Assume every object has a covering by
members of `\mathcal B`, and for each `V ∈ \mathcal B` there exist an integer `d_V ≥ 0` and a
cofinal system `\mathrm{Cov}_V` of coverings of `V` such that
`H^p(V_i, H^q(E)) = 0` for every member `V_i` of every covering in `\mathrm{Cov}_V` whenever
`p > d_V` and `q < 0`. Then every compatible comparison map
`E \to R\!\varprojlim_n \tau_{\ge -n} E` is an isomorphism in `D(\mathcal O)`. -/
theorem truncationComparison_isIso_of_basiswise_negative_cohomologySheaf_vanishing
    (X : RingedSite.{u, v})
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (E K : DerivedCategory (RingedSiteModuleCat X))
    (c : E ⟶ K)
    (hc : IsTruncationDerivedLimitComparison E K c)
    (B : Set X)
    (hcover :
      ∀ U : X, ∃ S : X.siteTopology.Cover U, ∀ I : S.Arrow, I.Y ∈ B)
    (hvanish :
      ∀ ⦃V : X⦄, V ∈ B →
        BasiswiseNegativeCohomologySheafVanishingData X E V) :
    IsIso c := sorry
