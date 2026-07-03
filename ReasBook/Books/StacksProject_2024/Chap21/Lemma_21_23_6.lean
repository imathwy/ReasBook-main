import Mathlib
import StacksProject_2024.Chap13.Definition_13_34_1
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
`U` of the ringed site `X`. -/
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

/-- The right derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`. -/
private abbrev ringedSiteDerivedSectionsOverObjectFunctor
    (X : RingedSite.{u, v}) (U : X)
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

/-- The degree-`m` objectwise cohomology group `H^m(U, K)` on the ringed site `X`. -/
private abbrev ringedSiteDerivedObjectwiseCohomology
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (m : ℤ) (K : DerivedCategory (RingedSiteModuleCat X)) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
    ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj K)

/-- The inverse system `n ↦ H^m(U, K_n)` attached to a sequential inverse system in
`D(\mathcal O_X)`. -/
private abbrev ringedSiteDerivedObjectwiseCohomologySystem
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X)) (m : ℤ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (Ksys ⋙ ringedSiteDerivedSectionsOverObjectFunctor X U) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m

/-- The canonical model for `R^1 \!\varprojlim_n H^m(U, K_n)` used by the Milnor short exact
sequence. -/
private abbrev ringedSiteDerivedObjectwiseR1LimitTerm
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X)) (m : ℤ) :
    AddCommGrpCat.{max u v} :=
  cokernel
    (CategoryTheory.derivedLimitDifferenceMap
      (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m))

/-- The transition morphism `H^m(U, K_j) ⟶ H^m(U, K_i)` attached to an inequality `i ≤ j`. -/
private abbrev ringedSiteDerivedObjectwiseCohomologyTransition
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X)) (m : ℤ)
    {i j : ℕ} (hij : i ≤ j) :
    (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m).obj (op j) ⟶
      (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m).obj (op i) :=
  (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m).map ((homOfLE hij).op)

/-- The projection from `\varprojlim_n H^m(U, K_n)` to the `n`th stage. -/
private abbrev ringedSiteDerivedObjectwiseCohomologyLimitProjection
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X)) (m : ℤ) (n : ℕ) :
    limit (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m) ⟶
      (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m).obj (op n) :=
  limit.π (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m) (op n)

/-- A Milnor comparison map over `U` for the tower `(K_n)` in degree `m`. This packages the
derived-limit hypothesis together with the short exact sequence used in the proof of the lemma. -/
private abbrev IsMilnorComparisonOver
    (X : RingedSite.{u, v}) (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X))
    (K : DerivedCategory (RingedSiteModuleCat X)) (m : ℤ)
    (π :
      ringedSiteDerivedObjectwiseCohomology X U m K ⟶
        limit (ringedSiteDerivedObjectwiseCohomologySystem X U Ksys m)) : Prop :=
  IsDerivedLimit Ksys K ∧
    ∃ (ι :
        ringedSiteDerivedObjectwiseR1LimitTerm X U Ksys (m - 1) ⟶
          ringedSiteDerivedObjectwiseCohomology X U m K)
      (hιπ : ι ≫ π = 0),
      (ShortComplex.mk ι π hιπ).ShortExact

-- Proof sketch: use the sheafification description of objectwise cohomology from Lemma `21.20.3`
-- to refine to a covering in the chosen cofinal family on which the image of a section vanishes at
-- stage `nV`. For each member of that cover, the Milnor short exact sequence and the vanishing of
-- the `R^1 lim` term identify `H^m(-, K)` with the inverse limit `lim_n H^m(-, K_n)`, and the
-- eventual injectivity hypothesis forces the local section itself to vanish. Since the
-- corresponding cohomology sheaf is obtained by sheafification, the original section must vanish.
/-- Lemma 21.23.6: let `X` be a ringed site, let `(K_n)` be a sequential inverse system in
`D(\mathcal O_X)`, let `V : X`, and let `m : ℤ`. Assume there is an integer `nV` and a cofinal
family `CovV` of coverings of `V` such that for every cover `T ∈ CovV` and every member
`I : T.Arrow`, the Milnor term `R^1 \!\varprojlim_n H^{m-1}(I.Y, K_n)` vanishes and the
transition maps `H^m(I.Y, K_n) → H^m(I.Y, K_{nV})` are injective for all `n ≥ nV`. Then every
Milnor comparison map `H^m(V, K) → \varprojlim_n H^m(V, K_n)` associated to the derived limit
`K = R \!\varprojlim_n K_n` becomes injective after projection to stage `nV`; this composite
formalizes the map `H^m(R \!\varprojlim_n K_n)(V) → H^m(K_{nV})(V)`. -/
theorem milnorComparisonToEventualStage_mono_of_cofinal_coverSystem
    (X : RingedSite.{u, v}) (V : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X))
    (K : DerivedCategory (RingedSiteModuleCat X))
    (m : ℤ) (nV : ℕ)
    (CovV : X.siteTopology.Cover V → Prop)
    (hcofinal :
      ∀ S : X.siteTopology.Cover V,
        ∃ T : X.siteTopology.Cover V, CovV T ∧ Nonempty (T ⟶ S))
    (hR1vanish :
      ∀ ⦃T : X.siteTopology.Cover V⦄, CovV T → ∀ I : T.Arrow,
        IsZero (ringedSiteDerivedObjectwiseR1LimitTerm X I.Y Ksys (m - 1)))
    (hinj :
      ∀ ⦃T : X.siteTopology.Cover V⦄, CovV T → ∀ I : T.Arrow, ∀ n : ℕ, ∀ hn : nV ≤ n,
        Mono
          (ringedSiteDerivedObjectwiseCohomologyTransition X I.Y Ksys m hn))
    {π :
      ringedSiteDerivedObjectwiseCohomology X V m K ⟶
        limit (ringedSiteDerivedObjectwiseCohomologySystem X V Ksys m)}
    (hπ : IsMilnorComparisonOver X V Ksys K m π) :
    Mono
      (π ≫ ringedSiteDerivedObjectwiseCohomologyLimitProjection X V Ksys m nV) := sorry
