import StacksProject_2024.Chap18.Definition_18_13_1
import StacksProject_2024.Chap21.Situation_21_25_1
import StacksProject_2024.Chap21.Situation_21_25_5
import StacksProject_2024.Chap21.Lemma_21_28_6

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
Domain-style sampling for Lemma 21.28.7:
- primary domain: unbounded derived pullback and right derived pushforward on ringed sites,
  restricted to the Chapter 13 cohomology-in full subcategories;
- sampled owner declarations:
  `derivedCategoryCohomologyInProperty`,
  `DerivedCategoryWithCohomologyIn`,
  `ObjectProperty.lift`,
  `modulePushforwardDerived_obj_mem_derivedCategoryWithCohomologyIn`;
- best owner abstraction: the Chapter 13 owner
  `DerivedCategoryWithCohomologyIn`, with restricted functors obtained by the canonical
  `ObjectProperty.lift`;
- primitive data: the morphism `f`, the weak Serre subcategories `A'` and `A`, the pullback
  membership hypothesis `hpull_mem`, the bounded-cohomology bases on `X` and along `f`, and the
  adjunction/unit data for `Rf_*`;
- derived API: the landing-property theorem for `Rf_*` under the local bounded-cohomology
  hypotheses and the resulting equivalence statement.

Source/core/bridge triage:
- `source-facing`: the local bounded-cohomology landing and equivalence statements of
  Lemma `21.28.7`;
- `core/canonical`: `derivedCategoryCohomologyInProperty`, `DerivedCategoryWithCohomologyIn`,
  `ObjectProperty.lift`, and the Chapter 21 restricted derived pullback equivalence theorem from
  Lemma `21.28.6`;
- `bridge/view`: the canonical inclusions of `DerivedCategoryWithCohomologyIn A` and
  `DerivedCategoryWithCohomologyIn A'` into the ambient derived categories.

The stronger hypotheses of Lemma `21.28.7` change only the proof that `Rf_*` lands in `D_{A'}`; they
do not justify a second restricted-pushforward owner parallel to the canonical
`modulePullbackDerivedOfFlatWithCohomologyIn` construction already publicized in
Lemma `21.28.6`. -/

variable (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A ((f^*).obj ℱ'))
variable [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategories f A' A hpull_mem)]

local notation "single0Y" => DerivedCategory.singleFunctor ModY (0 : ℤ)

-- Proof sketch: use the equivalence of
-- `modulePullbackOnWeakSerreSubcategories f A' A hpull_mem` together with the
-- unit-isomorphism hypothesis to
-- identify the higher direct images of objects of `A` with the corresponding vanishing and
-- degree-zero statements transported from `A'`. Apply the source-side bounded-cohomology basis and
-- the along-`f` bounded-cohomology basis from Situation `21.25.5` through Lemma `21.25.6` to pass
-- from bounded-below truncations to arbitrary unbounded objects, and conclude that `Rf_* K` has
-- all cohomology sheaves in `A'`.
section

variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [HasSheafify Y.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat)]
/-- The landing-property statement showing that, under the hypotheses of Lemma `21.28.7`, the
right derived pushforward carries `D_A(𝒪)` into `D_{A'}(𝒪')`. -/
theorem modulePushforwardDerived_obj_mem_derivedCategoryWithCohomologyIn_of_local_bounded_cohomology
    (basisX : BoundedCohomologyBasis X.structureSheaf A)
    (basisf : BoundedCohomologyBasis f A)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso
        ((modulePullbackDerived_pushforward_adjunction f).unit.app
          ((single0Y).obj ℱ'.obj)))
    (K : D_{A}) :
    derivedCategoryCohomologyInProperty A' ((R(f)_*).obj K.obj) := sorry

/-- Under the hypotheses of Lemma `21.28.7`, the adjunction unit is an isomorphism on every
object of `D_{A'}(𝒪_Y)`. -/
theorem modulePullbackDerivedOfFlatWithCohomologyIn_unit_app_isIso_of_local_bounded_cohomology
    (basisX : BoundedCohomologyBasis X.structureSheaf A)
    (basisf : BoundedCohomologyBasis f A)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso
        ((modulePullbackDerived_pushforward_adjunction f).unit.app
          ((single0Y).obj ℱ'.obj)))
    (K : D_{A'}) :
    IsIso ((modulePullbackDerived_pushforward_adjunction f).unit.app K.obj) := sorry

/-- Under the hypotheses of Lemma `21.28.7`, the adjunction counit is an isomorphism on every
object of `D_A(𝒪_X)`. -/
theorem modulePullbackDerivedOfFlatWithCohomologyIn_counit_app_isIso_of_local_bounded_cohomology
    (basisX : BoundedCohomologyBasis X.structureSheaf A)
    (basisf : BoundedCohomologyBasis f A)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso
        ((modulePullbackDerived_pushforward_adjunction f).unit.app
          ((single0Y).obj ℱ'.obj)))
    (K : D_{A}) :
    IsIso ((modulePullbackDerived_pushforward_adjunction f).counit.app K.obj) := sorry

-- Proof sketch: the bounded-below equivalence from Lemma `21.28.5` controls every truncation
-- `τ_{\ge -n} K`, while Lemma `21.25.6` gives the comparison isomorphisms
-- `H^j(Rf_* K) → H^j(Rf_*(τ_{\ge -n} K))` under the Situation `21.25.1` and `21.25.5`
-- hypotheses. Passing to the limit over truncations upgrades the bounded-below unit and counit
-- isomorphisms to all objects of the unbounded derived subcategories. This is the source-facing
-- equivalence criterion for the restricted pullback functor, without packaging a quasi-inverse
-- functorial equivalence datum in this file.
/-- Lemma 21.28.7: let `f : (𝒞, 𝒪) ⟶ (𝒞', 𝒪')` be a
morphism of ringed sites, let `A ⊆ Mod(𝒪)` and `A' ⊆ Mod(𝒪')` be weak Serre subcategories,
assume `f` is flat, assume the source-facing pullback functor
`modulePullbackOnWeakSerreSubcategories f A' A hpull_mem` is an
equivalence, assume
`ℱ' ⟶ Rf_* f^* ℱ'` is an isomorphism for `ℱ' ∈ A'`, assume `(𝒞, 𝒪, A)` satisfies Situation
`21.25.1`, and assume `f` and `A` satisfy Situation `21.25.5`. Then
the adjunction unit and counit for the restricted pullback and right derived pushforward are
isomorphisms on all objects of `D_{A'}(𝒪')` and `D_A(𝒪)`, respectively. This is the Prop-valued
equivalence criterion for `f^* : D_{A'}(𝒪') ⥤ D_A(𝒪)` furnished by the hypotheses of the lemma. -/
@[stacks 0D7W]
theorem
    modulePullbackDerivedOfFlatWithCohomologyIn_unit_and_counit_app_isIso_of_local_bounded_cohomology
    (basisX : BoundedCohomologyBasis X.structureSheaf A)
    (basisf : BoundedCohomologyBasis f A)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso
        ((modulePullbackDerived_pushforward_adjunction f).unit.app
          ((single0Y).obj ℱ'.obj))) :
    (∀ K : D_{A'},
      IsIso ((modulePullbackDerived_pushforward_adjunction f).unit.app K.obj)) ∧
      (∀ K : D_{A},
        IsIso ((modulePullbackDerived_pushforward_adjunction f).counit.app K.obj)) := sorry

end

end

end RingedSite.Hom
