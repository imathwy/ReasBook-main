import Mathlib
import StacksProject_2024.Chap15.Lemma_15_87_10
import StacksProject_2024.Chap18.Definition_18_6_1
import StacksProject_2024.Chap19.Lemma_19_13_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option synthInstance.maxHeartbeats 100000

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over a fixed object
`U` of the ringed site `X`. -/
abbrev ringedSiteSectionsOverObjectFunctor (X : RingedSite.{u, v}) (U : X) :
    SheafOfModules X.structureSheaf ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

-- Proof sketch: `SheafOfModules.toSheaf`, `sheafToPresheaf`, and evaluation at `U` are all
-- additive functors, so their composite `\Gamma(U,-)` is additive.
/-- The sections functor over a fixed object of a ringed site is additive. -/
theorem ringedSiteSectionsOverObjectFunctor_isAdditive
    (X : RingedSite.{u, v}) (U : X)
    [hAb : Abelian (SheafOfModules X.structureSheaf)] :
    @Functor.Additive
      (SheafOfModules X.structureSheaf) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteSectionsOverObjectFunctor X U) := sorry

/-- The right derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`. -/
abbrev ringedSiteDerivedSectionsOverObjectFunctor
    (X : RingedSite.{u, v}) (U : X)
    [hAb : Abelian (SheafOfModules X.structureSheaf)]
    [CategoryWithHomology (SheafOfModules X.structureSheaf)]
    [IsGrothendieckAbelian (SheafOfModules X.structureSheaf)]
    :
    DerivedCategory (SheafOfModules X.structureSheaf) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (SheafOfModules X.structureSheaf) AddCommGrpCat.{max u v}
    _ hAb _ AddCommGrpCat.instAbelian
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

-- Proof sketch: apply Lemma `19.13.6` to the sections functor `\Gamma(U,-)` to identify
-- `R\Gamma(U, K)` with a derived limit of the tower `n ↦ R\Gamma(U, K_n)`. Then apply the
-- Milnor short exact sequence of Lemma `15.87.10` to that inverse system in
-- `D(\operatorname{Ab})`.
/-- 21.23.4.1: for a ringed site `X`, an object `U : X`, a sequential inverse system `(K_n)` in
`D(\mathcal O_X)`, and a chosen derived limit `K`, the groups `H^m(U, K)` fit into the Milnor
short exact sequence
`0 \to R^1 \!\varprojlim_n H^{m-1}(U, K_n) \to H^m(U, K) \to \varprojlim_n H^m(U, K_n) \to 0`.
Here the left term is the canonical owner
`((Ksys ⋙ ringedSiteDerivedSectionsOverObjectFunctor X U) ⋙
  DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} (m - 1)).firstDerivedLimit`. -/
theorem ringedSiteDerivedSectionsOverObject_cohomology_shortExact_of_isDerivedLimit
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (SheafOfModules X.structureSheaf)]
    [CategoryWithHomology (SheafOfModules X.structureSheaf)]
    [IsGrothendieckAbelian (SheafOfModules X.structureSheaf)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules X.structureSheaf))
    (K : DerivedCategory (SheafOfModules X.structureSheaf))
    (hK : IsDerivedLimit Ksys K) (m : ℤ) :
    ∃ (ι :
        ((Ksys ⋙ ringedSiteDerivedSectionsOverObjectFunctor X U) ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} (m - 1)).firstDerivedLimit ⟶
          (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
            ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj K))
      (π :
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
            ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj K) ⟶
          limit
            ((Ksys ⋙ ringedSiteDerivedSectionsOverObjectFunctor X U) ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry
