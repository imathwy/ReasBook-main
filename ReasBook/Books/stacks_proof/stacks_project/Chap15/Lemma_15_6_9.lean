import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import stacks_proof.stacks_project.Chap10.Lemma_10_55_6
import stacks_proof.stacks_project.Chap15.«15_6_3_1»
import stacks_proof.stacks_project.Chap15.Situation_15_6_1

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

/- Domain-style sampling for Lemma 15.6.9:
- primary domain: finite projective modules in a surjective ring-pullback situation, expressed via
  full subcategories of module categories and the canonical base-change functor;
- sampled owner declarations:
  `finiteProjectiveModuleProperty`,
  `FiniteProjectiveModuleCat`,
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.lift`;
- best owner abstraction: the source-facing statement is the restricted base-change functor on the
  finite-projective full subcategories attached to the pullback square;
- primitive data: the surjective pullback situation `S`;
- derived API: the pullback-side finite-projective object property, the corresponding full
  subcategory, and the restricted base-change functor.

Source/core/bridge triage:
- `source-facing`: the finite-projective pullback property and the resulting equivalence statement;
- `core/canonical`: `finiteProjectiveModuleProperty`, `FiniteProjectiveModuleCat`, and the
  canonical base-change functor to the categorical pullback;
- `bridge/view`: the restricted base-change functor on the finite-projective full subcategories.
-/

/-- The object property on the pullback module category requiring finite projectivity of the
`B`-component and of the `A'`-component. -/
abbrev surjectiveRingPullbackFiniteProjectivePullbackProperty :
    ObjectProperty PBMod :=
  fun X ↦ finiteProjectiveModuleProperty B X.fst ∧ finiteProjectiveModuleProperty A' X.snd

/-- The full subcategory of pullback triples `(N, M', \varphi)` with `N` finite projective over
`B` and `M'` finite projective over `A'`. -/
abbrev SurjectiveRingPullbackFiniteProjectivePullbackCat :=
  (surjectiveRingPullbackFiniteProjectivePullbackProperty S).FullSubcategory

-- Proof sketch: the two components of the ambient base-change functor are scalar extensions along
-- `B' → B` and `B' → A'`. Finite projective modules remain finite projective after scalar
-- extension, so the base-change pullback object again has finite projective components.
/-- Base change from `B'` to the pullback category preserves finite projective modules. -/
theorem surjectiveRingPullbackModuleBaseChange_obj_mem_finiteProjectivePullbackProperty
    ⦃L' : ModuleCat S.Bprime⦄
    (hfinproj : finiteProjectiveModuleProperty S.Bprime L') :
    surjectiveRingPullbackFiniteProjectivePullbackProperty S
      ((baseChangeFunctor).obj L') := by
  -- The reduced file keeps only the public API; the objectwise finite-projective base-change
  -- proof is deferred together with the final equivalence argument.
  admit

/-- The base-change functor on the finite-projective full subcategories attached to a surjective
ring pullback situation. -/
noncomputable abbrev surjectiveRingPullbackFiniteProjectiveModuleBaseChangeFunctor :
    FiniteProjectiveModuleCat S.Bprime ⥤ SurjectiveRingPullbackFiniteProjectivePullbackCat S :=
  (surjectiveRingPullbackFiniteProjectivePullbackProperty S).lift
    ((finiteProjectiveModuleProperty S.Bprime).ι ⋙ baseChangeFunctor)
    (fun L' ↦
      surjectiveRingPullbackModuleBaseChange_obj_mem_finiteProjectivePullbackProperty S
        L'.property)

-- Proof sketch: this is the finite-projective analogue of Lemma `15.6.8 (3)`, obtained by
-- restricting the canonical base-change equivalence to the finite-projective full subcategories.
/-- Lemma 15.6.9: the category of finite projective `B'`-modules is equivalent to the full
subcategory of `Mod_B ×_{Mod_A} Mod_{A'}` consisting of triples `(N, M', \varphi)` with `N`
finite projective over `B` and `M'` finite projective over `A'`. -/
@[stacks 0D2J]
theorem surjectiveRingPullbackFiniteProjectiveModuleBaseChangeFunctor_isEquivalence :
    Functor.IsEquivalence
      (surjectiveRingPullbackFiniteProjectiveModuleBaseChangeFunctor S) := by
  -- The equivalence proof is the remaining finite-projective descent step.
  admit

end
