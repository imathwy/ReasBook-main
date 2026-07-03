import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite

noncomputable section

universe u v w z

/- Domain-style sampling for Lemma 21.24.2:
- primary domain: sequential inverse systems of cochain complexes of `\mathcal O_X`-modules on a
  ringed site, evaluated objectwise and then passed to cohomology sheaves;
- sampled owner declarations:
  `CategoryTheory.SequentialInverseSystem`,
  `CategoryTheory.SequentialInverseSystem.transitionMap`,
  `CategoryTheory.SequentialInverseSystem.IsMittagLeffler`,
  `limit.post`;
- best owner abstraction: the tower itself is a `SequentialInverseSystem`, while the canonical
  map `H^m(\varprojlim_n \mathcal F_n^\bullet) ⟶ \varprojlim_n H^m(\mathcal F_n^\bullet)` is the
  standard `limit.post` morphism for the composite with the cohomology-sheaf functor.

Source/core/bridge triage:
- `source-facing`: the final basiswise hypothesis theorem about the two cohomology-sheaf maps;
- `core/canonical`: `SequentialInverseSystem`, `.transitionMap`, `.IsMittagLeffler`, and
  `limit.post`;
- `bridge/view`: the objectwise degree/cohomology towers obtained from sections over `U`.

Primitive data are just the ringed site `X`, the tower `F`, the object `U`, and the degree `m`.
The transition maps, Mittag-Leffler conditions, and limit comparison morphism are derived API from
the owner abstractions above, so this file should reuse those owners directly rather than keep
parallel local copies.
-/

/-- The category of cochain complexes of `\mathcal O_X`-modules on the ringed site `X`. -/
abbrev ringedSiteComplex (X : RingedSite.{u, v}) :=
  CochainComplex (SheafOfModules X.structureSheaf) ℤ

/-- The sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over the fixed object `U`. -/
private abbrev ringedSiteSectionsOverObjectFunctor (X : RingedSite.{u, v}) (U : X) :
    SheafOfModules X.structureSheaf ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

/-- The inverse system of complexes of abelian groups obtained by taking sections over `U`
termwise. -/
private abbrev ringedSiteObjectwiseComplexInverseSystem (X : RingedSite.{u, v})
    (F : ℕᵒᵖ ⥤ ringedSiteComplex X) (U : X) :
    SequentialInverseSystem (CochainComplex AddCommGrpCat.{max u v} ℤ) :=
  F ⋙ (ringedSiteSectionsOverObjectFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The inverse system `n ↦ \mathcal F_n^m(U)` attached to a tower of complexes on a ringed site.
-/
abbrev ringedSiteObjectwiseDegreeInverseSystem (X : RingedSite.{u, v})
    (F : ℕᵒᵖ ⥤ ringedSiteComplex X) (U : X) (m : ℤ) :
    SequentialInverseSystem AddCommGrpCat.{max u v} :=
  ringedSiteObjectwiseComplexInverseSystem X F U ⋙
    HomologicalComplex.eval AddCommGrpCat.{max u v} (ComplexShape.up ℤ) m

/-- The inverse system `n ↦ H^m(\mathcal F_n^\bullet(U))` attached to a tower of complexes on a
ringed site. -/
abbrev ringedSiteObjectwiseCohomologyInverseSystem (X : RingedSite.{u, v})
    (F : ℕᵒᵖ ⥤ ringedSiteComplex X) (U : X) (m : ℤ) :
    SequentialInverseSystem AddCommGrpCat.{max u v} :=
  ringedSiteObjectwiseComplexInverseSystem X F U ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℤ) m

/-- The inverse system of degree-`m` cohomology sheaves of the tower
`(\mathcal F_n^\bullet)_n`. -/
abbrev ringedSiteCohomologySheafTower (X : RingedSite.{u, v})
    (F : ℕᵒᵖ ⥤ ringedSiteComplex X) (m : ℤ) :=
  F ⋙ HomologicalComplex.homologyFunctor (SheafOfModules X.structureSheaf) (ComplexShape.up ℤ) m ⋙
    SheafOfModules.toSheaf X.structureSheaf

/-- The canonical morphism
`H^m(\varprojlim_n \mathcal F_n^\bullet) ⟶ \varprojlim_n H^m(\mathcal F_n^\bullet)` on
underlying abelian sheaves. -/
abbrev ringedSiteCohomologySheafLimitComparison
    (X : RingedSite.{u, v})
    (F : ℕᵒᵖ ⥤ ringedSiteComplex X) (m : ℤ)
    [HasLimit F] [HasLimit (ringedSiteCohomologySheafTower X F m)] :
    (SheafOfModules.toSheaf X.structureSheaf).obj
        ((HomologicalComplex.homologyFunctor (SheafOfModules X.structureSheaf)
          (ComplexShape.up ℤ) m).obj (limit F)) ⟶
      limit (ringedSiteCohomologySheafTower X F m) :=
  limit.post F
    (HomologicalComplex.homologyFunctor (SheafOfModules X.structureSheaf)
      (ComplexShape.up ℤ) m ⋙ SheafOfModules.toSheaf X.structureSheaf)

-- Proof sketch: for each basis object `U ∈ B`, apply Lemma `15.87.3` to the tower of complexes
-- `\Gamma(U, \mathcal F_n^\bullet)` in degrees shifted by `m`; the hypotheses force the
-- comparison `H^m(\Gamma(U, \varprojlim_n \mathcal F_n^\bullet)) \to
-- \varprojlim_n H^m(\Gamma(U, \mathcal F_n^\bullet))` to be an isomorphism, and eventual
-- constancy identifies the latter with `H^m(\Gamma(U, \mathcal F_{n_0}^\bullet))`. Since every
-- object admits a cover by elements of `B`, the two resulting morphisms of abelian sheaves are
-- isomorphisms.
/-- Lemma 21.24.2: let `(\mathcal C, \mathcal O)` be a ringed site, let
`(\mathcal F_n^\bullet)_n` be an inverse system of complexes of `\mathcal O`-modules, and let
`m ∈ \mathbf Z`. If a subset `B` of objects covers the site, if for every `U ∈ B` the towers
`n ↦ \mathcal F_n^{m - 2}(U)`, `n ↦ \mathcal F_n^{m - 1}(U)`, and
`n ↦ H^{m - 1}(\mathcal F_n^\bullet(U))` have vanishing `R^1 \!\varprojlim`, and if the tower
`n ↦ H^m(\mathcal F_n^\bullet(U))` is constant from stage `n₀` on for every `U ∈ B`, then the
canonical maps
`H^m(\varprojlim_n \mathcal F_n^\bullet) ⟶ \varprojlim_n H^m(\mathcal F_n^\bullet) ⟶
H^m(\mathcal F_{n₀}^\bullet)` are isomorphisms of underlying abelian sheaves. -/
theorem cohomologySheafLimitComparison_and_projection_isIso_of_basiswise_vanishing_r1lim
    (X : RingedSite.{u, v})
    (F : ℕᵒᵖ ⥤ ringedSiteComplex X) (m : ℤ) (B : Set X) (n₀ : ℕ)
    [CategoryWithHomology (SheafOfModules X.structureSheaf)]
    [HasLimit F]
    [HasLimit (ringedSiteCohomologySheafTower X F m)]
    (hcover : ∀ V : X, ∃ S : X.siteTopology.Cover V, ∀ I : S.Arrow, I.Y ∈ B)
    (hdeg_m_sub_two : ∀ U : X, U ∈ B →
      IsMittagLeffler (ringedSiteObjectwiseDegreeInverseSystem X F U (m - 2)))
    (hdeg_m_sub_one : ∀ U : X, U ∈ B →
      IsMittagLeffler (ringedSiteObjectwiseDegreeInverseSystem X F U (m - 1)))
    (hcohom_m_sub_one : ∀ U : X, U ∈ B →
      IsMittagLeffler
        (ringedSiteObjectwiseCohomologyInverseSystem X F U (m - 1)))
    (heventually_constant : ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ h : n₀ ≤ n,
      IsIso ((ringedSiteObjectwiseCohomologyInverseSystem X F U m).transitionMap h))
    :
    IsIso (ringedSiteCohomologySheafLimitComparison X F m) ∧
      IsIso (limit.π (ringedSiteCohomologySheafTower X F m) (op n₀)) := sorry
