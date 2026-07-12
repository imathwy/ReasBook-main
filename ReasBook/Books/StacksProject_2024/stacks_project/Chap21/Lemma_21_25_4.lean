import StacksProject_2024.Chap13.Lemma_13_17_1
import StacksProject_2024.Chap13.Remark_13_34_5
import StacksProject_2024.Chap21.Lemma_21_7_4_core
import StacksProject_2024.Chap21.Lemma_21_19_1_core
import StacksProject_2024.Chap21.Lemma_21_20_3
import StacksProject_2024.Chap21.Situation_21_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped RingedSite.Hom
open scoped RingedSiteDerived
open scoped RingedSiteCohomology
open scoped DerivedCategoryWithCohomologyIn

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y

variable [Abelian ModX] [Abelian ModY]

/- Domain-style sampling for Lemma 21.25.4:
- primary domain: unbounded derived direct image on ringed sites, restricted to the canonical
  full subcategories cut out by cohomology lying in weak Serre classes;
- sampled owner declarations:
  `ModuleCat`,
  `f.modulePushforward`,
  `higherDirectImageModule`,
  `ObjectProperty.IsWeakSerreClass`,
  `derivedCategoryCohomologyInProperty`,
  `DerivedCategoryWithCohomologyIn`,
  `modulePushforwardToDerived`,
  `modulePushforwardDerived`;
- best owner abstraction: the cohomology condition should be phrased through the Chapter 13 owner
  `derivedCategoryCohomologyInProperty` and its full subcategory `DerivedCategoryWithCohomologyIn`,
  while the closure package on `A` and `A'` should be reused through the canonical owner class
  `IsWeakSerreClass`; the module categories should be reused through the Chapter 21 owner
  `ModuleCat`, and the unbounded derived pushforward and its higher direct images should be
  reused through the underived owner `f.modulePushforward`, the Chapter 21 higher-direct-image
  owner `higherDirectImageModule f`, and the corresponding Chapter 21 owner
  `modulePushforwardDerived f`;
- primitive data: the morphism `f`, the weak Serre owners `A` and `A'`, the bounded-cohomology
  bases on `X` and `Y`, and the higher-direct-image hypotheses `h_mem` and `h_vanish`;
- derived API: the landing theorem `Rf_* : D_{A} ⟶ D_{A'}` under those hypotheses and the
  owner truncation-range comparison theorem.

Source/core/bridge triage:
- `source-facing`: Lemma 21.25.4 (1) and (2), namely the landing property for `Rf_*` on
  `D_{A}` and the truncation-range comparison on its cohomology sheaves;
- `core/canonical`: `f.modulePushforward`, `modulePushforwardToDerived`,
  `modulePushforwardDerived`, `IsWeakSerreClass`, `higherDirectImageModule`,
  `derivedCategoryCohomologyInProperty`, and `DerivedCategoryWithCohomologyIn`;
- `bridge/view`: the inclusion functors `ObjectProperty.ι` from `D_{A}` and `D_{A'}` into the
  ambient derived categories.

The closure assumptions on `A` and `A'` are therefore not primitive public data here: the
canonical owner `[IsWeakSerreClass _]` already packages the needed closure behavior. -/

variable (A : ObjectProperty ModX)
variable [IsWeakSerreClass A]
variable [pushforwardAdditive : f.modulePushforward.Additive]
variable [injectiveResolutions : HasInjectiveResolutions (SheafOfModules X.structureSheaf)]
variable [hasRightDerived :
  Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

section

variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [HasSheafify Y.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat)]

variable (A' : ObjectProperty ModY)
variable [IsWeakSerreClass A']

-- Proof sketch: use Lemma `21.25.2` on `X` to rewrite `K` as the derived limit of its lower
-- truncations. By the bounded-below Leray spectral sequence, the assumptions `h_mem` and
-- `h_vanish` force each bounded-below stage `Rf_*(τ_{\ge -n} K)` to lie in `D_{A'}`. Applying
-- Lemma `21.25.3` on `Y` to the inverse system of these stages shows that the limit object
-- `Rf_* K` again has all cohomology sheaves in `A'`.
/-- Lemma 21.25.4 (1): if both `X` and `Y` satisfy Situation `21.25.1`, if every higher direct
image `R^p f_* 𝓕` of an object `𝓕 ∈ A` lies in `A'`, and if these higher direct images vanish
for `p > N`, then the unbounded right derived pushforward `Rf_*` carries `D_{A}` into `D_{A'}`. -/
@[stacks 0D6U]
theorem modulePushforwardDerived_obj_mem_derivedCategoryWithCohomologyIn_of_higherDirectImage_mem
    (basisX : BoundedCohomologyBasis X.structureSheaf A)
    (basisY : BoundedCohomologyBasis Y.structureSheaf A')
    (N : ℤ)
    (h_mem : ∀ ⦃ℱ : ModX⦄ (p : ℕ), A ℱ → A' (R^{p}_[f](ℱ)))
    (h_vanish : ∀ ⦃ℱ : ModX⦄ (p : ℕ), A ℱ → N < p →
      Limits.IsZero (R^{p}_[f](ℱ)))
    (K : D_{A}) :
    derivedCategoryCohomologyInProperty A' ((R(f)_*).obj K.obj) := sorry

end

-- Proof sketch: specialize the truncation-range control for unbounded right derived functors to
-- `f_*`. The bound `R^p f_* = 0` for `p > N`, together with the fact that the cohomology sheaves
-- of `K` lie in `A`, gives the usual spectral-sequence comparison showing that replacing `K` by
-- its lower truncation in degrees `≥ -n` does not change `H^j(Rf_* K)` once `j ≥ N - n`.

section

variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]

/-- Lemma 21.25.4 (2): if the higher direct images of objects of `A` vanish above the bound `N`,
then for `K ∈ D_{A}` the canonical map from `𝓗[j](Y, Rf_* K)` to the degree-`j` cohomology sheaf
of `Rf_*` applied to the lower truncation of `K` in degrees `≥ -n` is an isomorphism whenever
`j ≥ N - n`. -/
@[stacks 0D6U]
theorem modulePushforwardDerived_homologyMap_isIso_to_truncationGEStage
    (basisX : BoundedCohomologyBasis X.structureSheaf A)
    (N : ℤ)
    (h_vanish : ∀ ⦃ℱ : ModX⦄ (p : ℕ), A ℱ → N < p →
      Limits.IsZero (R^{p}_[f](ℱ)))
    (K : D_{A})
    (n : ℕ)
    (j : ℤ)
    (hj : N - (n : ℤ) ≤ j) :
    IsIso
      (((R(f)_*) ⋙ DerivedCategory.homologyFunctor ModY j).map
        (derivedTruncationGEToStage K.obj n)) := sorry

end

end

end RingedSite.Hom
