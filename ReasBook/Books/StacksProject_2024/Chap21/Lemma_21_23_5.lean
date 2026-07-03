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

section

variable (X : RingedSite.{u, v})

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
abbrev RingedSiteModuleCat :=
  SheafOfModules X.structureSheaf

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

/-- The sequential inverse system in `D(\mathcal O_X)` obtained from a tower of sheaves by
placing every stage in degree `0`. -/
abbrev ringedSiteModuleTowerInDerived
    [Abelian (RingedSiteModuleCat X)]
    (Fsys : ℕᵒᵖ ⥤ RingedSiteModuleCat X) :
    ℕᵒᵖ ⥤ DerivedCategory (RingedSiteModuleCat X) :=
  Fsys ⋙ ringedSiteSingleFunctorZero X

/-- The canonical model for the `R^1 \!\varprojlim` term of the tower of section groups
`n ↦ \mathcal F_n(U)`. -/
abbrev ringedSiteSectionsR1LimitTerm
    (U : X)
    (Fsys : ℕᵒᵖ ⥤ RingedSiteModuleCat X) :
    AddCommGrpCat.{max u v} :=
  cokernel (derivedLimitDifferenceMap (Fsys ⋙ ringedSiteSectionsOverObjectFunctor X U))

end

section

variable (X : RingedSite.{u, v})

variable [Abelian (RingedSiteModuleCat X)]
variable [CategoryWithHomology (RingedSiteModuleCat X)]
variable [IsGrothendieckAbelian (RingedSiteModuleCat X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]

variable (B : Set X)
variable (Fsys : ℕᵒᵖ ⥤ RingedSiteModuleCat X)
variable (K : DerivedCategory (RingedSiteModuleCat X))

-- Proof sketch: use Remark `21.23.4` objectwise on each `U ∈ B`. Since every stage `\mathcal F_n`
-- is concentrated in degree `0` and has no higher cohomology on `U`, the Milnor exact sequence
-- shows the higher objectwise cohomology of the chosen derived limit `K` vanishes on `B`. Then
-- Lemma `21.20.3` identifies the cohomology sheaf with the sheafification of this basiswise-zero
-- presheaf, so the higher cohomology sheaves of `K` vanish.
/-- Lemma 21.23.5 (1): if a subset `B` covers the ringed site `X`, if every stage `\mathcal F_n`
has vanishing higher cohomology on objects of `B`, and if the section towers
`n ↦ \mathcal F_n(U)` have vanishing `R^1 \!\varprojlim` for `U ∈ B`, then every nonzero
cohomology sheaf of a chosen derived limit `K = R\!\varprojlim_n \mathcal F_n` vanishes. This
is the higher-degree part of the statement `R\!\varprojlim_n \mathcal F_n = \varprojlim_n
\mathcal F_n`. -/
theorem derivedLimit_higherCohomologySheaf_isZero_of_basiswise_acyclic
    (hK : IsDerivedLimit (ringedSiteModuleTowerInDerived X Fsys) K)
    (hcover : ∀ V : X, ∃ S : X.siteTopology.Cover V, ∀ I : S.Arrow, I.Y ∈ B)
    (hacyclic :
      ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ p : ℤ, 0 < p →
        IsZero (ringedSiteModuleObjectwiseCohomology X U p (Fsys.obj (op n))))
    (hR1lim :
      ∀ U : X, U ∈ B → IsZero (ringedSiteSectionsR1LimitTerm X U Fsys))
    (q : ℤ) (hq : q ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (RingedSiteModuleCat X) q).obj K) := sorry

-- Proof sketch: apply the same objectwise Milnor exact sequence on each `U ∈ B`. The positive
-- degree terms vanish by hypothesis, and the `R^1 \!\varprojlim` term on sections vanishes by
-- assumption, so the degree-zero objectwise cohomology of `K` identifies with
-- `\varprojlim_n \mathcal F_n(U)` on the basis. Sheafifying with Lemma `21.20.3` identifies the
-- degree-zero cohomology sheaf of `K` with the ordinary inverse limit sheaf.
/-- Lemma 21.23.5 (2): under the same hypotheses, the degree-zero cohomology sheaf of a chosen
derived limit `K = R\!\varprojlim_n \mathcal F_n` is isomorphic to the ordinary inverse limit
sheaf `\varprojlim_n \mathcal F_n`. This is the degree-zero part of the statement
`R\!\varprojlim_n \mathcal F_n = \varprojlim_n \mathcal F_n`. -/
theorem derivedLimit_zeroCohomologySheaf_isomorphic_limit_of_basiswise_acyclic
    (hK : IsDerivedLimit (ringedSiteModuleTowerInDerived X Fsys) K)
    (hcover : ∀ V : X, ∃ S : X.siteTopology.Cover V, ∀ I : S.Arrow, I.Y ∈ B)
    (hacyclic :
      ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ p : ℤ, 0 < p →
        IsZero (ringedSiteModuleObjectwiseCohomology X U p (Fsys.obj (op n))))
    (hR1lim :
      ∀ U : X, U ∈ B → IsZero (ringedSiteSectionsR1LimitTerm X U Fsys))
    :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (RingedSiteModuleCat X) (0 : ℤ)).obj K)
      (limit Fsys) := sorry

-- Proof sketch: combine the degree-zero identification from part `(2)` with the vanishing of the
-- higher cohomology sheaves from part `(1)`. Evaluating over a basis object `U ∈ B` recovers the
-- higher cohomology of the ordinary inverse limit sheaf and shows it vanishes.
/-- Lemma 21.23.5 (3): under the same hypotheses, the ordinary inverse limit sheaf
`\varprojlim_n \mathcal F_n` has vanishing higher cohomology on every basis object `U ∈ B`. -/
theorem limit_objectwiseCohomology_isZero_of_basiswise_acyclic
    (hK : IsDerivedLimit (ringedSiteModuleTowerInDerived X Fsys) K)
    (hcover : ∀ V : X, ∃ S : X.siteTopology.Cover V, ∀ I : S.Arrow, I.Y ∈ B)
    (hacyclic :
      ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ p : ℤ, 0 < p →
        IsZero (ringedSiteModuleObjectwiseCohomology X U p (Fsys.obj (op n))))
    (hR1lim :
      ∀ U : X, U ∈ B → IsZero (ringedSiteSectionsR1LimitTerm X U Fsys))
    (U : X) (hU : U ∈ B) (p : ℤ) (hp : 0 < p) :
    IsZero (ringedSiteModuleObjectwiseCohomology X U p (limit Fsys)) := sorry

end
