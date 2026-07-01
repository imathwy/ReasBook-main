import Mathlib
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
    (U : X) :
    DerivedCategory (RingedSiteModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
    _ _ _ _
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

/-- The degree-`q` objectwise cohomology group `H^q(U, K)` on the ringed site `X`. -/
private abbrev ringedSiteDerivedObjectwiseCohomology
    (U : X) (q : ℤ) (K : DerivedCategory ModX) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} q).obj
    ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj K)

/-- The degree-`p` cohomology group `H^p(U, \mathcal F)` of a sheaf of `\mathcal O_X`-modules,
viewed via the embedding into `D(\mathcal O_X)` concentrated in degree `0`. -/
private abbrev ringedSiteModuleObjectwiseCohomology
    (U : X) (p : ℤ) (ℱ : ModX) :
    AddCommGrpCat.{max u v} :=
  ringedSiteDerivedObjectwiseCohomology X U p
    ((DerivedCategory.singleFunctor ModX (0 : ℤ)).obj ℱ)

-- Proof sketch: apply the spectral sequence of Lemma `13.21.3` to the sections functor
-- `\Gamma(U,-)` and to the bounded-below truncations `\tau_{\ge -n} K`. The basiswise
-- higher-cohomology vanishing hypothesis forces the spectral sequence to degenerate on every
-- `U ∈ B`, so for each truncation one gets
-- `H^q(U, \tau_{\ge -n}K) ≅ H^0(U, H^q(\tau_{\ge -n}K))`. For `n` large relative to `q`, the
-- right-hand side stabilizes to `H^0(U, H^q(K))`. Combine this stabilization with the Milnor
-- short exact sequence for `R\Gamma(U,-)` and the truncation-limit comparison from Lemma
-- `21.23.10` to identify `H^q(U, K)` with `H^0(U, H^q(K))`.
/-- Lemma 21.23.11: let `(\mathcal C, \mathcal O)` be a ringed site, let `K` be an object of
`D(\mathcal O)`, and let `\mathcal B` be a subset of objects such that every object admits a
covering by members of `\mathcal B`. If for every `U ∈ \mathcal B` and all `p > 0`, `q ∈ \mathbf
Z` one has `H^p(U, H^q(K)) = 0`, then for every `U ∈ \mathcal B` and `q ∈ \mathbf Z` the
derived cohomology group `H^q(U, K)` is naturally identified with the degree-zero sections
`H^0(U, H^q(K))` of the `q`-th cohomology sheaf. -/
theorem ringedSiteDerivedObjectwiseCohomology_iso_zeroDegree_of_basiswise_cohomologySheafAcyclic
    (K : DerivedCategory ModX)
    (B : Set X)
    (hcover :
      ∀ W : X, ∃ S : X.siteTopology.Cover W, ∀ I : S.Arrow, I.Y ∈ B)
    (hacyclic :
      ∀ ⦃U : X⦄, U ∈ B → ∀ p q : ℤ, 0 < p →
        IsZero
          (ringedSiteModuleObjectwiseCohomology X U p
            ((DerivedCategory.homologyFunctor ModX q).obj K)))
    ⦃U : X⦄ (hU : U ∈ B) (q : ℤ) :
    IsIsomorphic
      (ringedSiteDerivedObjectwiseCohomology X U q K)
      (ringedSiteModuleObjectwiseCohomology X U 0
        ((DerivedCategory.homologyFunctor ModX q).obj K)) := sorry

end
