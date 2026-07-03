import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import stacks_project.Chap18.Definition_18_31_1
import stacks_project.Chap18.Lemma_18_24_4
import stacks_project.Chap21.Remark_21_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [f.IsFlat]
variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

variable (A' : ObjectProperty (ModuleCat Y)) (A : ObjectProperty (ModuleCat X))
variable [_root_.CategoryTheory.ObjectProperty.IsWeakSerreClass A']
variable [_root_.CategoryTheory.ObjectProperty.IsWeakSerreClass A]

/-- The object property on `D(\mathcal O_Z)` consisting of those complexes whose cohomology
sheaves lie in the chosen subcategory `B`. -/
abbrev moduleDerivedCohomologyInProperty
    (Z : RingedSite.{u, v}) (B : ObjectProperty (ModuleCat Z)) :
    ObjectProperty (ModuleDerived Z) :=
  fun K ↦ ∀ n : ℤ, B ((DerivedCategory.homologyFunctor (ModuleCat Z) n).obj K)

/-- The object property on `D(\mathcal O_Z)` consisting of bounded-below complexes whose
cohomology sheaves lie in `B`. -/
abbrev moduleDerivedBoundedBelowCohomologyInProperty
    (Z : RingedSite.{u, v}) (B : ObjectProperty (ModuleCat Z)) :
    ObjectProperty (ModuleDerived Z) :=
  fun K ↦ moduleDerivedCohomologyInProperty Z B K ∧ ∃ n : ℤ, K.IsGE n

/-- The bounded-below derived full subcategory on `Z` cut out by the cohomology condition `B`. -/
abbrev ModuleDerivedPlusWithCohomologyIn
    (Z : RingedSite.{u, v}) (B : ObjectProperty (ModuleCat Z)) :=
  (moduleDerivedBoundedBelowCohomologyInProperty Z B).FullSubcategory

local notation "DplusY" => ModuleDerivedPlusWithCohomologyIn Y A'
local notation "DplusX" => ModuleDerivedPlusWithCohomologyIn X A
local notation "PplusY" => moduleDerivedBoundedBelowCohomologyInProperty Y A'
local notation "PplusX" => moduleDerivedBoundedBelowCohomologyInProperty X A

/-- The exact-functor package on module sheaves attached to pullback along a flat morphism of
ringed sites. -/
noncomputable abbrev flatModulePullbackExactFunctor : ModuleCat Y ⥤ₑ ModuleCat X :=
  let _ : CategoryTheory.Limits.PreservesFiniteLimits f.modulePullback :=
    ((CategoryTheory.exactFunctor_iff f.modulePullback).mp
      IsFlat.pullback_exact).1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits f.modulePullback :=
    ((CategoryTheory.exactFunctor_iff f.modulePullback).mp
      IsFlat.pullback_exact).2
  ExactFunctor.of f.modulePullback

/-- The pullback functor on derived categories induced by the exact pullback on module sheaves for
a flat morphism of ringed sites. -/
noncomputable abbrev flatModulePullbackDerived : ModuleDerived Y ⥤ ModuleDerived X :=
  let _ : (flatModulePullbackExactFunctor f).obj.Additive :=
    (inferInstance : f.modulePullback.Additive)
  (flatModulePullbackExactFunctor f).obj.mapDerivedCategory

local notation "fStarDerived" => flatModulePullbackDerived f

/-- A module sheaf on a ringed site, viewed as a derived object concentrated in degree `0`. -/
abbrev moduleObjectAsDerived (Z : RingedSite.{u, v}) (ℱ : ModuleCat Z) :
    ModuleDerived Z :=
  (DerivedCategory.singleFunctor (ModuleCat Z) (0 : ℤ)).obj ℱ

/-- The pullback functor on weak Serre subcategories induced by pullback on module sheaves. -/
abbrev modulePullbackOnWeakSerreSubcategory
    (hpull_mem : ∀ ⦃ℱ' : ModuleCat Y⦄, A' ℱ' → A (f.modulePullback.obj ℱ')) :
    A'.FullSubcategory ⥤ A.FullSubcategory :=
  ObjectProperty.lift A (A'.ι ⋙ f.modulePullback) (fun ℱ' ↦ hpull_mem ℱ'.property)

-- Proof sketch: bounded-belowness is preserved by the exact derived pullback attached to a flat
-- morphism, and exactness identifies the cohomology sheaves of `f^* K` with the pullbacks of the
-- cohomology sheaves of `K`. The hypothesis `hpull_mem` then shows that these cohomology sheaves
-- lie in `A`.
/-- Exact pullback along a flat morphism of ringed sites sends `D^+_{A'}(\mathcal O_Y)` to
`D^+_A(\mathcal O_X)`. -/
theorem modulePullbackDerivedOfFlat_obj_mem_derivedCategoryPlusWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModuleCat Y⦄, A' ℱ' → A (f.modulePullback.obj ℱ')) (K : DplusY) :
    PplusX ((ObjectProperty.ι PplusY ⋙ fStarDerived).obj K) := sorry

/-- The pullback functor on bounded-below derived categories with cohomology in the chosen weak
Serre subcategories. -/
abbrev modulePullbackDerivedOfFlatPlusWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModuleCat Y⦄, A' ℱ' → A (f.modulePullback.obj ℱ')) :
    DplusY ⥤ DplusX :=
  ObjectProperty.lift PplusX
    (ObjectProperty.ι PplusY ⋙ fStarDerived)
    (modulePullbackDerivedOfFlat_obj_mem_derivedCategoryPlusWithCohomologyIn
      f A' A hpull_mem)

-- Proof sketch: by essential surjectivity of `f^* : A'.FullSubcategory ⥤ A.FullSubcategory`,
-- every cohomology sheaf of `K ∈ D^+_A(\mathcal O_X)` is isomorphic to `f^* ℱ'` for some
-- `ℱ' ∈ A'`. The unit hypothesis identifies `ℱ'` with `Rf_* f^* ℱ'`, forcing the higher direct
-- images of `f^* ℱ'` to vanish and the degree-zero direct image to lie in `A'`. The spectral
-- sequence `R^p f_* H^q(K) ⇒ H^{p+q}(Rf_* K)` then shows that `Rf_* K` is bounded below and all of
-- its cohomology sheaves lie in `A'`.
/-- Under the hypotheses of Lemma `21.28.5`, the right derived pushforward sends
`D^+_A(\mathcal O_X)` to `D^+_{A'}(\mathcal O_Y)`. -/
theorem modulePushforwardDerived_obj_mem_derivedCategoryPlusWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModuleCat Y⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A hpull_mem)]
    (adj : fStarDerived ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj)))
    (K : DplusX) :
    PplusY ((ObjectProperty.ι PplusX ⋙ modulePushforwardDerived f).obj K) := sorry

/-- The right derived pushforward restricted to the bounded-below derived subcategory with
cohomology in `A`. In Lemma `21.28.5`, this is the quasi-inverse to the restricted pullback
functor. -/
abbrev modulePushforwardDerivedPlusWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModuleCat Y⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A hpull_mem)]
    (adj : fStarDerived ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    DplusX ⥤ DplusY :=
  ObjectProperty.lift PplusY
    (ObjectProperty.ι PplusX ⋙ modulePushforwardDerived f)
    (modulePushforwardDerived_obj_mem_derivedCategoryPlusWithCohomologyIn
      f A' A hpull_mem adj hunit)

-- Proof sketch: Lemma `21.28.4` upgrades the unit-isomorphism hypothesis from degree-zero objects
-- `ℱ'[0]` with `ℱ' ∈ A'` to every bounded-below object of `D^+_{A'}(\mathcal O_Y)`, giving full
-- faithfulness of the restricted pullback. The previous helper theorem shows that the restricted
-- pushforward lands in `D^+_{A'}(\mathcal O_Y)`, and Lemmas `21.28.2`, `21.28.3`, and `4.24.4`
-- then identify it as the quasi-inverse.
/-- Lemma 21.28.5: let `f : X ⟶ Y` be a flat morphism of ringed sites, let
`A' ⊆ \operatorname{Mod}(\mathcal O_Y)` and `A ⊆ \operatorname{Mod}(\mathcal O_X)` be weak Serre
subcategories, assume pullback induces an equivalence `A' ≌ A`, and assume the adjunction unit
`ℱ'[0] ⟶ Rf_* f^*(ℱ'[0])` is an isomorphism for every `ℱ' ∈ A'`. Then the induced pullback functor
`f^* : D^+_{A'}(\mathcal O_Y) ⥤ D^+_A(\mathcal O_X)` is an equivalence of categories. The
restricted right derived pushforward defined below is the intended quasi-inverse. -/
theorem modulePullbackDerivedOfFlatPlusWithCohomologyIn_isEquivalence
    (hpull_mem : ∀ ⦃ℱ' : ModuleCat Y⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A hpull_mem)]
    (adj : fStarDerived ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    Functor.IsEquivalence
      (modulePullbackDerivedOfFlatPlusWithCohomologyIn f A' A hpull_mem) := sorry

/-- The equivalence instance attached to Lemma `21.28.5`. -/
noncomputable instance instModulePullbackDerivedOfFlatPlusWithCohomologyInIsEquivalence
    (hpull_mem : ∀ ⦃ℱ' : ModuleCat Y⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A hpull_mem)]
    (adj : fStarDerived ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    Functor.IsEquivalence
      (modulePullbackDerivedOfFlatPlusWithCohomologyIn f A' A hpull_mem) :=
  modulePullbackDerivedOfFlatPlusWithCohomologyIn_isEquivalence f A' A hpull_mem adj hunit

end

end RingedSite.Hom
