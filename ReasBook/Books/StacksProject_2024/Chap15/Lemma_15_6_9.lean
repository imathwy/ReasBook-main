import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap15.Situation_15_6_1
import StacksProject_2024.Chap15.Lemma_15_6_7
import StacksProject_2024.Chap15.Lemma_15_6_8
import StacksProject_2024.Chap15.Lemma_15_13_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u

noncomputable section

section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

local notation "PBMod" =>
  CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)

local notation "baseChangeFunctor" =>
  moduleCatBaseChangeToCategoricalPullback
    S.toA
    S.fromAprime
    S.bprimeToB
    S.bprimeToAprime
    S.comm

local notation "fiberProductFunctor" =>
  module_tensor_pullback_right_adjoint
    S.bprimeToB
    S.bprimeToAprime
    S.comm

/- Domain-style sampling for Lemma 15.6.9:
- primary domain: finite projective modules in a surjective ring-pullback situation, expressed via
  full subcategories of module categories and the canonical base-change/fibre-product functors;
- sampled owner declarations:
  `finiteProjectiveModuleProperty`,
  `FiniteProjectiveModuleCat`,
  `surjectiveRingPullbackFlatPullbackProperty`,
  `ObjectProperty.FullSubcategory`;
- best owner abstraction: the main owner data remain
  `finiteProjectiveModuleProperty`/`FiniteProjectiveModuleCat` from Chapter 10, together with the
  canonical pullback functors from Lemmas `15.6.7` and `15.6.8`; the pullback-side finite
  projective condition is derived from those owners, not a second root notion;
- primitive data: the surjective pullback situation `S` and the canonical pullback object
  `X : PBMod`;
- derived API: the pullback-side finite-projective property and the restricted functors on the
  corresponding full subcategories.

Source/core/bridge triage:
- `source-facing`: the finite-projective pullback property and the resulting equivalence statement;
- `core/canonical`: `finiteProjectiveModuleProperty`, `FiniteProjectiveModuleCat`, and the
  canonical base-change/fibre-product functors;
- `bridge/view`: the restricted functors between the finite-projective full subcategories. -/

/-- The object property on the pullback module category requiring finite projectivity of the
`B`-component and of the `A'`-component. -/
abbrev surjectiveRingPullbackFiniteProjectivePullbackProperty
    : ObjectProperty PBMod :=
  fun X ↦ finiteProjectiveModuleProperty B X.fst ∧ finiteProjectiveModuleProperty A' X.snd

/-- The full subcategory of pullback triples `(N, M', \varphi)` with `N` finite projective over
`B` and `M'` finite projective over `A'`. -/
abbrev SurjectiveRingPullbackFiniteProjectivePullbackCat
    :=
  (surjectiveRingPullbackFiniteProjectivePullbackProperty S).FullSubcategory

-- Proof sketch: finite projective modules are flat and finitely presented, hence finite.
-- Extension of scalars along `B' → B` and `B' → A'` preserves finite projective modules, so the
-- base-change triple associated to a finite projective `B'`-module lies in the finite-projective
-- pullback subcategory.
/-- Base change from `B'` to the pullback category preserves finite projective modules. -/
theorem surjectiveRingPullbackModuleBaseChange_obj_mem_finiteProjectivePullbackProperty
    ⦃L' : ModuleCat S.Bprime⦄
    (hfinproj : finiteProjectiveModuleProperty S.Bprime L') :
    surjectiveRingPullbackFiniteProjectivePullbackProperty S
      ((baseChangeFunctor).obj L') := sorry

/-- The base-change functor on the finite-projective full subcategories attached to a surjective
ring pullback situation. -/
noncomputable abbrev surjectiveRingPullbackFiniteProjectiveModuleBaseChangeFunctor
    :
    FiniteProjectiveModuleCat S.Bprime ⥤ SurjectiveRingPullbackFiniteProjectivePullbackCat S :=
  (surjectiveRingPullbackFiniteProjectivePullbackProperty S).lift
    ((finiteProjectiveModuleProperty S.Bprime).ι ⋙ (baseChangeFunctor))
    (fun L' ↦
      surjectiveRingPullbackModuleBaseChange_obj_mem_finiteProjectivePullbackProperty S
        L'.property)

-- Proof sketch: by Algebra, Lemma `10.78.2`, finite projective modules are finitely presented and
-- flat. Lemma `15.6.8` gives flatness of the fibre-product module, while Lemma `15.6.7` gives its
-- finiteness; the finite-presentation argument in the textbook then upgrades this to finite
-- projectivity.
/-- The fibre-product functor sends pullback triples with finite projective components to finite
projective modules over the fibre-product ring. -/
theorem surjectiveRingPullbackModuleFiberProduct_finiteProjective
    ⦃X : PBMod⦄
    (hfinproj : surjectiveRingPullbackFiniteProjectivePullbackProperty S X) :
    finiteProjectiveModuleProperty S.Bprime ((fiberProductFunctor).obj X) := sorry

/-- The fibre-product functor on the finite-projective full subcategories attached to a
surjective ring pullback situation. -/
noncomputable abbrev surjectiveRingPullbackFiniteProjectiveModuleFiberProductFunctor
    :
    SurjectiveRingPullbackFiniteProjectivePullbackCat S ⥤ FiniteProjectiveModuleCat S.Bprime :=
  (finiteProjectiveModuleProperty S.Bprime).lift
    ((surjectiveRingPullbackFiniteProjectivePullbackProperty S).ι ⋙ (fiberProductFunctor))
    (fun X ↦ surjectiveRingPullbackModuleFiberProduct_finiteProjective S X.property)

-- Proof sketch: finite projective modules are exactly finitely presented flat modules. The flat
-- equivalence of Lemma `15.6.8` identifies the relevant pullback triples, and the finiteness
-- argument of Lemma `15.6.9` shows that the fibre-product functor preserves finite presentation,
-- yielding an equivalence on the finite-projective full subcategories.
/-- Lemma 15.6.9: the category of finite projective `B'`-modules is equivalent to the full
subcategory of `Mod_B ×_{Mod_A} Mod_{A'}` consisting of triples `(N, M', \varphi)` with `N`
finite projective over `B` and `M'` finite projective over `A'`. -/
theorem surjectiveRingPullbackFiniteProjectiveModuleBaseChangeFunctor_isEquivalence
    :
    Functor.IsEquivalence
      (surjectiveRingPullbackFiniteProjectiveModuleBaseChangeFunctor S) := sorry

end
