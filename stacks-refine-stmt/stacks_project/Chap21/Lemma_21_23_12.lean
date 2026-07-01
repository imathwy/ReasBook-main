import Mathlib
import stacks_project.Chap13.Definition_13_34_1
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
abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

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
    (U : X) :
    DerivedCategory (RingedSiteModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
    _ _ _ _
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

/-- The degree-`p` objectwise cohomology group `H^p(U, K)` of a derived `\mathcal O_X`-module
`K`. -/
abbrev ringedSiteDerivedObjectwiseCohomology
    (U : X) (p : ℤ) (K : DerivedCategory (RingedSiteModuleCat X)) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} p).obj
    ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj K)

/-- The degree-`p` cohomology group `H^p(U, \mathcal F)` of a sheaf of `\mathcal O_X`-modules,
viewed via the derived-category embedding in degree `0`. -/
abbrev ringedSiteModuleObjectwiseCohomology
    (U : X) (p : ℤ) (ℱ : RingedSiteModuleCat X) :
    AddCommGrpCat.{max u v} :=
  ringedSiteDerivedObjectwiseCohomology X U p
    ((DerivedCategory.singleFunctor (RingedSiteModuleCat X) (0 : ℤ)).obj ℱ)

/-- The inverse system `n ↦ H^q(K_n)` of cohomology sheaves of a sequential inverse system in
`D(\mathcal O_X)`. -/
abbrev ringedSiteCohomologySheafTower
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X)) (q : ℤ) :
    ℕᵒᵖ ⥤ RingedSiteModuleCat X :=
  Ksys ⋙ DerivedCategory.homologyFunctor (RingedSiteModuleCat X) q

/-- The canonical model for `R^1 \!\varprojlim_n H^0(U, H^q(K_n))` on a basis object `U`. -/
abbrev ringedSiteCohomologySheafSectionsR1LimitTerm
    (U : X) (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X)) (q : ℤ) :
    AddCommGrpCat.{max u v} :=
  cokernel
    (CategoryTheory.derivedLimitDifferenceMap
      ((ringedSiteCohomologySheafTower X Ksys q) ⋙
        ringedSiteSectionsOverObjectFunctor X U))

-- Proof sketch: for each `U ∈ B`, apply Lemma `21.23.11` to the derived-limit object `K` and use
-- the basiswise acyclicity of the cohomology sheaves to identify `H^q(U, K)` with
-- `H^0(U, H^q(K))`. Apply Remark `21.23.4` to the tower `R\Gamma(U, K_n)` and the vanishing of
-- `R^1 \!\varprojlim_n H^0(U, H^q(K_n))` to identify `H^q(U, K)` with the inverse limit of the
-- sections of `H^q(K_n)` over `U`. Since every object admits a cover by members of `B`, the
-- sheafification of this basiswise presheaf identity gives the claimed isomorphism of cohomology
-- sheaves.
/-- Lemma 21.23.12: let `X` be a ringed site, let `(K_n)` be an inverse system in
`D(\mathcal O_X)`, and let `K = R\!\varprojlim_n K_n` be a chosen derived limit. If a subset
`B` of objects covers the site, if for every `U ∈ B`, every stage `K_n`, and every `q ∈ \mathbf
Z` the cohomology sheaf `H^q(K_n)` has vanishing higher cohomology on `U`, and if the inverse
system `n ↦ H^0(U, H^q(K_n))` has vanishing `R^1 \!\varprojlim` on every `U ∈ B`, then for each
`q ∈ \mathbf Z` the `q`-th cohomology sheaf of `K` is isomorphic to the inverse limit of the
cohomology sheaves `H^q(K_n)`. -/
theorem derivedLimit_cohomologySheaf_isomorphic_limit_of_basiswise_cohomologySheaf_acyclic
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X))
    (K : DerivedCategory (RingedSiteModuleCat X))
    (hK : IsDerivedLimit Ksys K)
    (B : Set X)
    (hcover : ∀ W : X, ∃ S : X.siteTopology.Cover W, ∀ I : S.Arrow, I.Y ∈ B)
    (hacyclic :
      ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ q p : ℤ, 0 < p →
        IsZero
          (ringedSiteModuleObjectwiseCohomology X U p
            ((DerivedCategory.homologyFunctor (RingedSiteModuleCat X) q).obj
              (Ksys.obj (op n)))))
    (hR1lim :
      ∀ U : X, U ∈ B → ∀ q : ℤ,
        IsZero (ringedSiteCohomologySheafSectionsR1LimitTerm X U Ksys q))
    (q : ℤ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (RingedSiteModuleCat X) q).obj K)
      (limit (ringedSiteCohomologySheafTower X Ksys q)) := sorry

end
