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

section

variable (X : RingedSite.{u, v})

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat :=
  SheafOfModules X.structureSheaf

local notation "ModX" => RingedSiteModuleCat X

variable [Abelian (RingedSiteModuleCat X)]
variable [CategoryWithHomology (RingedSiteModuleCat X)]
variable [IsGrothendieckAbelian (RingedSiteModuleCat X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over a fixed object
`U` of the ringed site `X`, viewed on underlying abelian groups. -/
private abbrev ringedSiteSectionsOverObjectFunctor (U : X) :
    RingedSiteModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

-- Proof sketch: `SheafOfModules.toSheaf`, `sheafToPresheaf`, and evaluation at `U` are additive,
-- so their composite sections functor is additive as well.
/-- The sections functor over a fixed object of a ringed site is additive. -/
private theorem ringedSiteSectionsOverObjectFunctor_isAdditive
    (U : X)
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
    (U : X)
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
    (U : X)
    (p : ℤ) (ℱ : RingedSiteModuleCat X) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} p).obj
    ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj
      ((DerivedCategory.singleFunctor (RingedSiteModuleCat X) (0 : ℤ)).obj ℱ))

-- Proof sketch: apply Lemma `21.23.8` with the constant bound `d_V = d` for every basis object
-- `V ∈ B`, and let `Cov_V` be the coverings of `V` all of whose members lie in `B`. The covering
-- hypothesis makes each `Cov_V` cofinal, and the stated vanishing assumption is exactly the
-- required hypothesis on the negative cohomology sheaves `H^q(E)`.
/-- Lemma 21.23.10: let `(\mathcal C, \mathcal O)` be a ringed site, let `E ∈ D(\mathcal O)`,
and assume there exist an integer `d ≥ 0` and a subset `B` of objects of `\mathcal C` such that
every object admits a covering by members of `B` and
`H^p(V, H^q(E)) = 0` for `p > d`, `q < 0`, and `V ∈ B`. Then any compatible comparison map
from `E` to a chosen derived limit of the truncation tower `(\tau_{\ge -n} E)_n`, i.e. any
formalization of the canonical map `E \to R\!\varprojlim_n \tau_{\ge -n} E` from
Remark `13.34.5`, is an isomorphism in `D(\mathcal O)`. -/
theorem truncationComparison_isIso_of_uniform_basiswise_negative_cohomologySheaf_vanishing
    (E K : DerivedCategory (SheafOfModules X.structureSheaf))
    (c : E ⟶ K)
    (hc : IsTruncationDerivedLimitComparison E K c)
    (d : ℤ) (hd : 0 ≤ d)
    (B : Set X)
    (hcover :
      ∀ U : X, ∃ S : X.siteTopology.Cover U, ∀ I : S.Arrow, I.Y ∈ B)
    (hvanish :
      ∀ ⦃V : X⦄, V ∈ B → ∀ p q : ℤ, d < p → q < 0 →
        IsZero
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} p).obj
            ((ringedSiteDerivedSectionsOverObjectFunctor X V).obj
              ((DerivedCategory.singleFunctor (SheafOfModules X.structureSheaf) (0 : ℤ)).obj
                ((DerivedCategory.homologyFunctor (SheafOfModules X.structureSheaf) q).obj
                  E))))) :
    IsIso c := sorry

end
