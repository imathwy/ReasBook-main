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

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over a fixed object
`U` of the ringed site `X`. -/
private abbrev ringedSiteSectionsOverObjectFunctor (X : RingedSite.{u, v}) (U : X) :
    SheafOfModules X.structureSheaf ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

-- Proof sketch: `SheafOfModules.toSheaf`, `sheafToPresheaf`, and evaluation at `U` are additive,
-- so their composite `\Gamma(U,-)` is additive.
/-- The sections functor over a fixed object of a ringed site is additive. -/
private theorem ringedSiteSectionsOverObjectFunctor_isAdditive
    (X : RingedSite.{u, v}) (U : X)
    [hAb : Abelian (SheafOfModules X.structureSheaf)] :
    @Functor.Additive
      (SheafOfModules X.structureSheaf) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteSectionsOverObjectFunctor X U) := sorry

/-- The right derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`. -/
private abbrev ringedSiteDerivedSectionsOverObjectFunctor
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (SheafOfModules X.structureSheaf)]
    [CategoryWithHomology (SheafOfModules X.structureSheaf)]
    [IsGrothendieckAbelian (SheafOfModules X.structureSheaf)] :
    DerivedCategory (SheafOfModules X.structureSheaf) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (SheafOfModules X.structureSheaf) AddCommGrpCat.{max u v}
    _ _ _ _
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

-- Proof sketch: apply the derived-functor preservation of homotopy limits from
-- `CategoryTheory.additiveFunctor_totalRightDerived_preservesDerivedLimit` to the sections
-- functor `\Gamma(U,-)`, and then apply the Milnor short exact sequence for the resulting inverse
-- system in `D(\operatorname{Ab})`.
/-- Remark 21.23.4: for a ringed site `X`, an object `U : X`, a sequential inverse system
`(K_n)` in `D(\mathcal O_X)`, and a chosen derived limit `K = R\!\varprojlim K_n`, the
objectwise cohomology groups `H^m(U, K)` fit into the Milnor short exact sequence
`0 \to R^1 \!\varprojlim_n H^{m-1}(U, K_n) \to H^m(U, K) \to \varprojlim_n H^m(U, K_n) \to 0`.
This is the formal content of the displayed exact sequence `21.23.4.1` in the remark; the
surrounding discussion about sheafification versus inverse limit is recorded here only in the
docstring. -/
theorem ringedSiteDerivedLimit_objectwiseCohomologyShortExact
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (SheafOfModules X.structureSheaf)]
    [CategoryWithHomology (SheafOfModules X.structureSheaf)]
    [IsGrothendieckAbelian (SheafOfModules X.structureSheaf)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules X.structureSheaf))
    (K : DerivedCategory (SheafOfModules X.structureSheaf))
    (hK : IsDerivedLimit Ksys K) (m : ℤ) :
    ∃ (ι :
        cokernel
            (CategoryTheory.derivedLimitDifferenceMap
              ((Ksys ⋙ ringedSiteDerivedSectionsOverObjectFunctor X U) ⋙
                DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} (m - 1))) ⟶
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
