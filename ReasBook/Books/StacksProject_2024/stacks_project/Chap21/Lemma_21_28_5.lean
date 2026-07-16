import StacksProject_2024.stacks_project.Chap13.Lemma_13_17_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_14_5_Leray_spectral_sequence
import StacksProject_2024.stacks_project.Chap21.Lemma_21_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open scoped RingedSite.Hom
open scoped DerivedCategoryWithCohomologyIn

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y

variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [Fact (IsFlat f)]
variable (A' : ObjectProperty ModY) (A : ObjectProperty ModX)
variable [IsWeakSerreClass A']
variable [IsWeakSerreClass A]

end

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y

variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [Fact (IsFlat f)]
variable [f.modulePushforward.Additive]
variable [(f^*).Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyCategoryToDerivedBelow f.modulePushforward)
  (boundedBelowHomotopyQuasiIso ModX)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

variable (A' : ObjectProperty (ModuleCat Y)) (A : ObjectProperty (ModuleCat X))
variable [IsWeakSerreClass A']
variable [IsWeakSerreClass A]

/-
Domain-style sampling for Lemma 21.28.5:
- primary domain: bounded-below derived pullback and right derived pushforward on ringed sites,
  restricted to the Chapter 13 cohomology-in full subcategories;
- sampled owner declarations:
  `derivedCategoryBoundedBelowCohomologyInProperty`,
  `DerivedCategoryPlusWithCohomologyIn`,
  `ObjectProperty.lift`,
  `modulePushforwardDerivedPlus`,
  `modulePullbackDerived_pushforward_adjunction`;
- best owner abstraction:
  together with the canonical `ObjectProperty.lift` expressions that restrict these ambient
  functors to the bounded-below cohomology-in subcategories; flat pullback is handled through the
  ambient owner `modulePullbackDerived f`,
  while bounded-below pushforward reuses the chapter owner `modulePushforwardDerivedPlus f` and
  the Chapter 21 derived adjunction owner `modulePullbackDerived_pushforward_adjunction f`
  supplies the unit map;
- primitive data: the flat morphism `f`, the weak Serre subcategories `A'` and `A`, and the
  pullback membership hypothesis `hpull_mem`;
- derived API: the landing-property theorems for `f^*` and `Rf_*`, together with the resulting
  equivalence statement for the canonical `ObjectProperty.lift` restriction of derived pullback.

Source/core/bridge triage:
- `source-facing`: the bounded-below restricted pullback/pushforward landing statements and the
  resulting equivalence statement of Lemma 21.28.5;
- `core/canonical`: `derivedCategoryBoundedBelowCohomologyInProperty`, `ObjectProperty.lift`,
  `modulePushforwardDerivedPlus`, and `modulePullbackDerived_pushforward_adjunction`;
- `bridge/view`: the inclusion functors `ObjectProperty.ι PX` and `ObjectProperty.ι PY` into the
  ambient bounded-below derived categories.

This file therefore keeps the source-facing landing theorems and equivalence statement, exposes
the induced bounded-below cohomology-in functors through explicit canonical `ObjectProperty.lift`
expressions in theorem statements, and still reuses the canonical Chapter 21 adjunction owner
instead of quantifying over a parallel local adjunction parameter. -/

variable (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A ((f^*).obj ℱ'))
local notation "DModX" => D⁺(ModX)
local notation "DModY" => D⁺(ModY)
local notation "plusX" => (t.plus : ObjectProperty (ModuleDerived X))
local notation "plusY" => (t.plus : ObjectProperty (ModuleDerived Y))
local notation "PX" => derivedCategoryBoundedBelowCohomologyInProperty A
local notation "PY" => derivedCategoryBoundedBelowCohomologyInProperty A'
local notation "plusYι" => ObjectProperty.ι plusY

/-- The pullback functor on the weak Serre full subcategories
`A'.FullSubcategory ⥤ A.FullSubcategory` induced by `hpull_mem`. -/
abbrev modulePullbackOnWeakSerreSubcategories
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A ((f^*).obj ℱ')) :
    A'.FullSubcategory ⥤ A.FullSubcategory :=
  A.lift (A'.ι ⋙ f^*) (fun ℱ' : A'.FullSubcategory ↦ hpull_mem ℱ'.property)

local instance : Abelian ModX := SheafOfModules.instAbelian X.structureSheaf
local instance : Abelian ModY := SheafOfModules.instAbelian Y.structureSheaf

theorem modulePullbackDerived_obj_mem_boundedBelowDerivedCategory (K : DModY) :
    plusX ((plusYι ⋙ modulePullbackDerived f).obj K) :=
  sorry

/-- The bounded-below derived pullback functor induced by a flat morphism of ringed sites. -/
abbrev modulePullbackDerivedPlusOfFlat :
    DModY ⥤ DModX :=
  ObjectProperty.lift plusX
    (plusYι ⋙ modulePullbackDerived f)
    (modulePullbackDerived_obj_mem_boundedBelowDerivedCategory f)

local notation "single0Y" => DerivedCategory.singleFunctor ModY (0 : ℤ)

-- Proof sketch: bounded-belowness is preserved by the exact derived pullback attached to a flat
-- morphism, and exactness identifies the cohomology sheaves of `f^* K` with the pullbacks of the
-- cohomology sheaves of `K`. The hypothesis `hpull_mem` then shows that these cohomology sheaves
-- lie in `A`.
/-- Exact pullback along a flat morphism of ringed sites sends `D⁺_{A'}(𝒪_Y)` to
`D⁺_A(𝒪_X)`. -/
theorem modulePullbackDerivedOfFlat_obj_mem_derivedCategoryPlusWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A ((f^*).obj ℱ'))
    (K : D⁺_{A'}) :
    PX ((ObjectProperty.ι PY ⋙ modulePullbackDerivedPlusOfFlat f).obj K) :=
  sorry

/-- Exact pullback along a flat morphism of ringed sites, restricted to the bounded-below derived
subcategories cut out by the weak Serre subcategories `A'` and `A`. -/
abbrev modulePullbackDerivedOfFlatPlusWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A ((f^*).obj ℱ')) :
    D⁺_{A'} ⥤ D⁺_{A} :=
  ObjectProperty.lift PX
    (ObjectProperty.ι PY ⋙ modulePullbackDerivedPlusOfFlat f)
    (modulePullbackDerivedOfFlat_obj_mem_derivedCategoryPlusWithCohomologyIn
      f A' A hpull_mem)

-- Proof sketch: by essential surjectivity of `f^* : A'.FullSubcategory ⥤ A.FullSubcategory`,
-- every cohomology sheaf of `K ∈ D⁺_A(𝒪_X)` is isomorphic to `f^* ℱ'` for some
-- `ℱ' ∈ A'`. The unit hypothesis identifies `ℱ'` with `Rf_* f^* ℱ'`, forcing the higher direct
-- images of `f^* ℱ'` to vanish and the degree-zero direct image to lie in `A'`. The spectral
-- sequence `R^p f_* H^q(K) ⇒ H^{p+q}(Rf_* K)` then shows that `Rf_* K` is bounded below and all of
-- its cohomology sheaves lie in `A'`.
/-- Under the hypotheses of Lemma `21.28.5`, the right derived pushforward sends
`D⁺_A(𝒪_X)` to `D⁺_{A'}(𝒪_Y)`. -/
theorem modulePushforwardDerived_obj_mem_derivedCategoryPlusWithCohomologyIn
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategories f A' A hpull_mem)]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow f.modulePushforward)
      (boundedBelowHomotopyQuasiIso ModX)]
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (((modulePullbackDerived_pushforward_adjunction f).unit.app)
        ((single0Y).obj ℱ'.obj)))
    (K : D⁺_{A}) :
    PY ((ObjectProperty.ι PX ⋙ modulePushforwardDerivedPlus f).obj K) :=
  sorry

-- Proof sketch: Lemma `21.28.4` upgrades the unit-isomorphism hypothesis from degree-zero objects
-- `ℱ'[0]` with `ℱ' ∈ A'` to every bounded-below object of `D⁺_{A'}(𝒪_Y)`, giving full
-- faithfulness of the restricted pullback. The previous helper theorem shows that the restricted
-- pushforward lands in `D⁺_{A'}(𝒪_Y)`, and Lemmas `21.28.2`, `21.28.3`, and `4.24.4`
-- then identify it as the quasi-inverse.
/-- Lemma 21.28.5: let `f : X ⟶ Y` be a flat morphism of ringed sites, let
`A' ⊆ Mod(𝒪_Y)` and `A ⊆ Mod(𝒪_X)` be weak Serre subcategories, assume pullback induces an
equivalence `A' ≌ A`, and assume the adjunction unit `ℱ'[0] ⟶ Rf_* f^*(ℱ'[0])` is an isomorphism
for every `ℱ' ∈ A'`. Then the induced pullback functor
`modulePullbackDerivedOfFlatPlusWithCohomologyIn f A' A hpull_mem :
  D⁺_{A'}(𝒪_Y) ⥤ D⁺_A(𝒪_X)` is an equivalence of categories. -/
@[stacks 0D7U]
theorem modulePullbackDerivedOfFlatPlusWithCohomologyIn_isEquivalence
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategories f A' A hpull_mem)]
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (((modulePullbackDerived_pushforward_adjunction f).unit.app)
        ((single0Y).obj ℱ'.obj))) :
    Functor.IsEquivalence (modulePullbackDerivedOfFlatPlusWithCohomologyIn f A' A hpull_mem) := by
  let _ := hunit
  sorry

instance instModulePullbackDerivedOfFlatPlusWithCohomologyInIsEquivalence
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategories f A' A hpull_mem)]
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (((modulePullbackDerived_pushforward_adjunction f).unit.app)
        ((single0Y).obj ℱ'.obj))) :
    Functor.IsEquivalence (modulePullbackDerivedOfFlatPlusWithCohomologyIn f A' A hpull_mem) := by
  let _ := hunit
  exact modulePullbackDerivedOfFlatPlusWithCohomologyIn_isEquivalence f A' A hpull_mem hunit

end

end RingedSite.Hom
