import StacksProject_2024.Chap12.Definition_12_10_1
import StacksProject_2024.Chap13.Lemma_13_17_1
import StacksProject_2024.Chap21.Lemma_21_19_1
import StacksProject_2024.Chap21.Situation_21_25_1
import StacksProject_2024.Chap21.Lemma_21_28_4
import StacksProject_2024.Chap21.Lemma_21_28_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.ObjectProperty
open scoped RingedSite.Hom
open scoped RingedSiteDerived
open scoped DerivedCategoryWithCohomologyIn

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y

variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [HasSheafify Y.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat)]

variable [Abelian ModX] [Abelian ModY]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [Fact (IsFlat f)]
variable [f.modulePushforward.Additive]
variable [(f^*).Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

variable (A' : ObjectProperty ModY) (A : ObjectProperty ModX)
variable [IsWeakSerreClass A']
variable [IsWeakSerreClass A]

/-
Domain-style sampling for Lemma 21.28.6:
- primary domain: exact derived pullback and right derived pushforward on ringed sites, restricted
  to the full subcategories cut out by weak-Serre cohomology conditions;
- sampled owner declarations:
  `derivedCategoryCohomologyInProperty`,
  `DerivedCategoryWithCohomologyIn`,
  `ObjectProperty.lift`,
  `f^*`;
- best owner abstraction: the Chapter 13 owner
  `DerivedCategoryWithCohomologyIn` built from `derivedCategoryCohomologyInProperty`, with the
  restricted functors obtained by the canonical `ObjectProperty.lift`, both on the derived
  categories and on the weak-Serre full subcategories;
- primitive data: the morphism `f`, the weak Serre subcategories `A'` and `A`, the pullback
  membership hypothesis `hpull_mem`, the bounded-cohomology bases on `X` and `Y`, and the
  adjunction/unit data for `Rf_*`;
- derived API: the landing-property theorems for pullback and pushforward, the restricted
  functors, and the resulting equivalence statement.

Source/core/bridge triage:
- `source-facing`: the restricted derived pullback/pushforward statements of Lemma `21.28.6`;
- `core/canonical`: `derivedCategoryCohomologyInProperty`, `DerivedCategoryWithCohomologyIn`,
  and `ObjectProperty.lift`;
- `bridge/view`: the inclusions `PX.ι` and `PY.ι` into the ambient
  derived categories.

This file therefore should not introduce a second owner for the cohomology condition: it reuses
the Chapter 13 owner and only adds the source-facing restricted functors on top of it. -/
private abbrev PX : ObjectProperty (DerivedCategory ModX) :=
  derivedCategoryCohomologyInProperty A
private abbrev PY : ObjectProperty (DerivedCategory ModY) :=
  derivedCategoryCohomologyInProperty A'

variable (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A ((f^*).obj ℱ'))
local notation "single0Y" => DerivedCategory.singleFunctor ModY (0 : ℤ)

-- Proof sketch: pullback along a flat morphism is exact, so on the derived category it commutes
-- with cohomology objects. If every cohomology sheaf of `K` lies in `A'`, then the hypothesis
-- `hpull_mem` implies every cohomology sheaf of `f^* K` lies in `A`.
/-- Exact pullback along a flat morphism of ringed sites sends
`D_{A'}(𝒪_Y)` to `D_A(𝒪_X)`. -/
theorem modulePullbackDerived_obj_mem_derivedCategoryWithCohomologyIn
    (K : D_{A'}) :
    PX ((PY.ι ⋙ modulePullbackDerived f).obj K) := sorry

/-- Exact derived pullback along a flat morphism of ringed sites, restricted to the full
subcategories `D_{A'}(𝒪_Y)` and `D_A(𝒪_X)` cut out by the weak Serre subcategories `A'` and
`A`. -/
abbrev modulePullbackDerivedOfFlatWithCohomologyIn :
    D_{A'} ⥤ D_{A} :=
  ObjectProperty.lift (derivedCategoryCohomologyInProperty A)
    ((derivedCategoryCohomologyInProperty A').ι ⋙ modulePullbackDerived f)
    (modulePullbackDerived_obj_mem_derivedCategoryWithCohomologyIn f A' A)

-- Proof sketch: first use the equivalence on `A'` together with the unit-isomorphism hypothesis
-- to obtain the degree-zero pushforward statements `R^0 f_* (f^* ℱ') ∈ A'` and
-- `R^p f_* (f^* ℱ') = 0` for `p > 0`. Essential surjectivity of pullback on `A'`
-- transfers these bounds to arbitrary objects of `A`. Then Lemma `21.25.4` with `N = 0`,
-- combined with the bounded-cohomology-basis hypotheses on `X` and `Y`, shows that `Rf_*`
-- carries every object of `D_A(𝒪_X)` into `D_{A'}(𝒪_Y)`.
/-- The landing-property statement showing that the right derived pushforward carries
`D_A(𝒪_X)` into `D_{A'}(𝒪_Y)`. This is the input needed to
restrict `Rf_*` by `ObjectProperty.lift` in Lemma `21.28.6`. -/
theorem modulePushforwardDerived_obj_mem_derivedCategoryWithCohomologyIn
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategories f A' A hpull_mem)]
    [HasSheafify X.siteTopology AddCommGrpCat]
    [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
    [HasSheafify Y.siteTopology AddCommGrpCat]
    [HasExt (Sheaf Y.siteTopology AddCommGrpCat)]
    (basisX : BoundedCohomologyBasis X.structureSheaf A)
    (basisY : BoundedCohomologyBasis Y.structureSheaf A')
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso
        ((modulePullbackDerived_pushforward_adjunction f).unit.app
          ((single0Y).obj ℱ'.obj)))
    (K : D_{A}) :
    PY ((PX.ι ⋙ R(f)_*).obj K) := sorry

/-- The restricted right derived pushforward on the cohomology-in full subcategories
`D_A(𝒪_X)` and `D_{A'}(𝒪_Y)`. Under the hypotheses of Lemma `21.28.6`, this is the canonical
quasi-inverse to `modulePullbackDerivedOfFlatWithCohomologyIn`. -/
abbrev modulePushforwardDerivedOnCohomologyIn
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategories f A' A hpull_mem)]
    [HasSheafify X.siteTopology AddCommGrpCat]
    [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
    [HasSheafify Y.siteTopology AddCommGrpCat]
    [HasExt (Sheaf Y.siteTopology AddCommGrpCat)]
    (basisX : BoundedCohomologyBasis X.structureSheaf A)
    (basisY : BoundedCohomologyBasis Y.structureSheaf A')
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso
        ((modulePullbackDerived_pushforward_adjunction f).unit.app
          ((single0Y).obj ℱ'.obj))) :
    D_{A} ⥤ D_{A'} :=
  ObjectProperty.lift (derivedCategoryCohomologyInProperty A')
    ((derivedCategoryCohomologyInProperty A).ι ⋙ R(f)_*)
    (modulePushforwardDerived_obj_mem_derivedCategoryWithCohomologyIn
      f A' A hpull_mem basisX basisY hunit)

-- Proof sketch: exact pullback commutes with the truncation functors `τ_{\ge -n}`, so the
-- restricted pullback on `D_{A'}` and the restricted pushforward on `D_A`
-- are compatible with truncations. Lemma `21.28.5` identifies these truncations as quasi-inverse
-- equivalences on the bounded-below subcategories, while Lemma `21.25.6` gives the truncation
-- control for `Rf_*` on unbounded objects. Passing to the limit over truncations shows that both
-- the unit `K' ⟶ Rf_* f^* K'` and the counit `f^* Rf_* K ⟶ K` are isomorphisms on the unbounded
-- derived subcategories, hence the restricted pullback is an equivalence with quasi-inverse the
-- restricted `Rf_*`.
/-- Lemma 21.28.6: let `f : X ⟶ Y` be a flat morphism of ringed topoi formalized by a flat
morphism of ringed sites, let `A ⊆ Mod(𝒪_X)` and `A' ⊆ Mod(𝒪_Y)` be weak Serre subcategories,
assume the source-facing pullback functor
`modulePullbackOnWeakSerreSubcategories f A' A hpull_mem` is an
equivalence, assume
`ℱ' ⟶ Rf_* f^* ℱ'` is an isomorphism for every `ℱ' ∈ A'`, and assume both
`(X, 𝒪_X, A)` and `(Y, 𝒪_Y, A')` satisfy Situation `21.25.1`. Then the induced exact pullback
functor `f^* : D_{A'}(𝒪_Y) ⥤ D_A(𝒪_X)` is an equivalence of
categories. The canonical restricted right derived pushforward
`modulePushforwardDerivedOnCohomologyIn f A' A hpull_mem basisX basisY hunit`
is the intended quasi-inverse. -/
@[stacks 0D7V]
theorem modulePullbackDerivedOfFlatWithCohomologyIn_isEquivalence
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategories f A' A hpull_mem)]
    [HasSheafify X.siteTopology AddCommGrpCat]
    [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
    [HasSheafify Y.siteTopology AddCommGrpCat]
    [HasExt (Sheaf Y.siteTopology AddCommGrpCat)]
    (basisX : BoundedCohomologyBasis X.structureSheaf A)
    (basisY : BoundedCohomologyBasis Y.structureSheaf A')
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso
        ((modulePullbackDerived_pushforward_adjunction f).unit.app
          ((single0Y).obj ℱ'.obj))) :
    Functor.IsEquivalence
      ((modulePullbackDerivedOfFlatWithCohomologyIn f A' A hpull_mem) : D_{A'} ⥤ D_{A}) := sorry

instance instModulePullbackDerivedOfFlatWithCohomologyInIsEquivalence
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategories f A' A hpull_mem)]
    [HasSheafify X.siteTopology AddCommGrpCat]
    [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
    [HasSheafify Y.siteTopology AddCommGrpCat]
    [HasExt (Sheaf Y.siteTopology AddCommGrpCat)]
    (basisX : BoundedCohomologyBasis X.structureSheaf A)
    (basisY : BoundedCohomologyBasis Y.structureSheaf A')
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso
        ((modulePullbackDerived_pushforward_adjunction f).unit.app
          ((single0Y).obj ℱ'.obj))) :
    Functor.IsEquivalence
      ((modulePullbackDerivedOfFlatWithCohomologyIn f A' A hpull_mem) : D_{A'} ⥤ D_{A}) :=
  by
    let _ := basisX
    let _ := basisY
    let _ := hunit
    exact
      modulePullbackDerivedOfFlatWithCohomologyIn_isEquivalence
        f A' A hpull_mem basisX basisY hunit
end

end RingedSite.Hom
