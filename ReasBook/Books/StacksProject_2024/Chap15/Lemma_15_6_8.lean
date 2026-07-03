import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap15.Situation_15_6_1
import StacksProject_2024.Chap15.Lemma_15_6_5

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CommRingCat

universe u

noncomputable section

section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']

/- Domain-style sampling for Lemma 15.6.8:
- primary domain: flat modules expressed as object properties on module categories, together with
  the canonical base-change and fibre-product functors across a pullback square of commutative
  rings;
- sampled owner declarations:
  `Module.Flat`,
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.lift`,
  `finiteProjectiveModuleProperty`;
- best owner abstraction: `flatModuleProperty R` is the reusable owner-level bridge from the
  canonical predicate `Module.Flat R` to the full-subcategory machinery, while the pullback-side
  flatness condition is the derived object property on the canonical categorical pullback module
  category;
- primitive data: the surjective pullback situation `S` and the canonical functors
  `moduleCatBaseChangeToCategoricalPullback ...` and `module_tensor_pullback_right_adjoint ...`;
- derived API: `FlatModuleCat R`, `surjectiveRingPullbackFlatPullbackProperty S`,
  `SurjectiveRingPullbackFlatPullbackCat S`, and the restricted functors between them.

Source/core/bridge triage:
- `source-facing`: the three parts of Lemma 15.6.8 about flatness of the fibre product and the
  induced equivalence on flat-module categories;
- `core/canonical`: `Module.Flat`, `flatModuleProperty`, `ObjectProperty.FullSubcategory`, and the
  canonical base-change/fibre-product functors from Lemmas `15.6.4` and `15.6.5`;
- `bridge/view`: the restricted functors on the flat full subcategories. -/

/-- The object property of flat modules over a commutative ring. -/
abbrev flatModuleProperty (R : Type u) [CommRing R] : ObjectProperty (ModuleCat R) :=
  fun M ↦ Module.Flat R M

/-- The full subcategory of `ModuleCat R` spanned by flat `R`-modules. -/
abbrev FlatModuleCat (R : Type u) [CommRing R] :=
  (flatModuleProperty R).FullSubcategory

section

variable (S : SurjectiveRingPullbackSituation B A A')

local notation "PBMod" =>
  CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)

/-- The object property on the pullback module category requiring flatness of the `B`-component and
of the `A'`-component. -/
abbrev surjectiveRingPullbackFlatPullbackProperty
    : ObjectProperty PBMod :=
  fun X ↦ Module.Flat B X.fst ∧ Module.Flat A' X.snd

/-- The full subcategory of pullback triples `(N, M', \varphi)` with `N` flat over `B` and `M'`
flat over `A'`. -/
abbrev SurjectiveRingPullbackFlatPullbackCat
    :=
  (surjectiveRingPullbackFlatPullbackProperty S).FullSubcategory

-- Proof sketch: the two components of
-- `moduleCatBaseChangeToCategoricalPullback S.toA S.fromAprime S.bprimeToB S.bprimeToAprime
-- S.comm` are extension-of-scalars functors along
-- `B' → B` and `B' → A'`. Flatness is preserved by base change, so a flat `B'`-module yields a
-- pullback triple whose `B`- and `A'`-components are flat.
/-- Base change from `B'` to the pullback category preserves flatness of modules. -/
theorem surjectiveRingPullbackModuleBaseChange_obj_mem_flatPullbackProperty
    ⦃L' : ModuleCat S.Bprime⦄
    (hflat : Module.Flat S.Bprime L') :
    surjectiveRingPullbackFlatPullbackProperty S
      ((moduleCatBaseChangeToCategoricalPullback
        S.toA
        S.fromAprime
        S.bprimeToB
        S.bprimeToAprime
        S.comm).obj L') := sorry

/-- The base-change functor on the flat-module full subcategories attached to a surjective ring
pullback situation. -/
noncomputable abbrev surjectiveRingPullbackFlatModuleBaseChangeFunctor
    :
    FlatModuleCat S.Bprime ⥤ SurjectiveRingPullbackFlatPullbackCat S :=
  (surjectiveRingPullbackFlatPullbackProperty S).lift
    ((flatModuleProperty S.Bprime).ι ⋙
      moduleCatBaseChangeToCategoricalPullback
        S.toA
        S.fromAprime
        S.bprimeToB
        S.bprimeToAprime
        S.comm)
    (fun L' ↦
      surjectiveRingPullbackModuleBaseChange_obj_mem_flatPullbackProperty S L'.property)

-- Proof sketch: argue as in the textbook with the ideal `J = ker(B' → B)` and the local
-- criterion for flatness modulo a nilpotent ideal. Flatness of `N` over `B` controls the part
-- away from `J`, while flatness of `M'` over `A'` identifies the `J`-torsion piece with an
-- injective tensor map over `A'`.
/-- Lemma 15.6.8 (1): if `(N, M', \varphi)` is a pullback triple with `N` flat over `B` and `M'`
flat over `A'`, then the fibre-product module `N ×_\varphi M'` is flat over `B' = B ×_A A'`. -/
theorem surjectiveRingPullbackModuleFiberProduct_flat
    ⦃X : PBMod⦄
    (hflat : surjectiveRingPullbackFlatPullbackProperty S X) :
    Module.Flat S.Bprime
      ((module_tensor_pullback_right_adjoint
        S.bprimeToB
        S.bprimeToAprime
        S.comm).obj X) := sorry

/-- The fibre-product functor on the flat-module full subcategories attached to a surjective ring
pullback situation. -/
noncomputable abbrev surjectiveRingPullbackFlatModuleFiberProductFunctor
    :
    SurjectiveRingPullbackFlatPullbackCat S ⥤ FlatModuleCat S.Bprime :=
  (flatModuleProperty S.Bprime).lift
    ((surjectiveRingPullbackFlatPullbackProperty S).ι ⋙
      module_tensor_pullback_right_adjoint
        S.bprimeToB
        S.bprimeToAprime
        S.comm)
    (fun X ↦ surjectiveRingPullbackModuleFiberProduct_flat S X.property)

-- Proof sketch: Lemma `15.6.5` already gives surjectivity of the adjunction map. For a flat
-- `B'`-module, the same injectivity criterion used in part `(1)` shows that the kernel vanishes,
-- so the canonical map from `L'` to the fibre product of its two base changes is an isomorphism.
/-- Lemma 15.6.8 (2): if `L'` is a flat `B'`-module, then the canonical adjunction unit
`L' ⟶ (L' ⊗[B'] B) ×_{L' ⊗[B'] A} (L' ⊗[B'] A')`
is an isomorphism, identifying `L'` with the fibre product of its two base changes. -/
theorem surjectiveRingPullbackModuleAdjunctionMap_isIso_of_flat
    (L' : ModuleCat S.Bprime)
    (hflat : Module.Flat S.Bprime L') :
    IsIso ((module_tensor_pullback_adjunction
      S.bprimeToB
      S.bprimeToAprime
      S.comm).unit.app L') := sorry

-- Proof sketch: the restricted base-change functor lands in the flat pullback full subcategory by
-- the helper theorem above, and part `(1)` gives the corresponding restricted fibre-product
-- functor. Part `(2)` supplies the unit isomorphisms, while the objectwise equalities from Lemma
-- `15.6.4` give the counit isomorphisms, so the restricted base-change functor is an equivalence.
/-- Lemma 15.6.8 (3): the category of flat `B'`-modules is equivalent to the full subcategory of
`Mod_B ×_{Mod_A} Mod_{A'}` consisting of triples `(N, M', \varphi)` with `N` flat over `B` and
`M'` flat over `A'`. -/
theorem surjectiveRingPullbackFlatModuleBaseChangeFunctor_isEquivalence
    :
    Functor.IsEquivalence (surjectiveRingPullbackFlatModuleBaseChangeFunctor S) := sorry

end

end
