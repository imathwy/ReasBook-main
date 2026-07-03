import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_6_2 (from Chap15) -/
open CategoryTheory Limits TopCat

universe u

noncomputable section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']

/- Domain-style sampling for 15.6.2:
- primary domain: prime-spectrum maps in `TopCat` and pushout squares in `CategoryTheory`;
- sampled owner declarations:
  `PrimeSpectrum.comap`,
  `PrimeSpectrum.continuous_comap`,
  `IsPushout`,
  `IsPushout.exists_desc`;
- best owner abstraction: the primitive source-facing data is still
  `S : SurjectiveRingPullbackSituation B A A'`; the induced maps on prime spectra are derived from
  the canonical owner `PrimeSpectrum.comap`, and the universal-property claim is owned by
  `IsPushout`;
- primitive data: the ring maps and surjectivity hypothesis stored in `S`;
- derived API: the topological-space object `S.specBprime` and the four canonical spectrum maps
  `S.specToB`, `S.specToAprime`, `S.specBToBprime`, and `S.specAprimeToBprime`.

Source/core/bridge triage:
- `source-facing`: the pushout statement for the spectrum square of Situation `15.6.1`;
- `core/canonical`: `PrimeSpectrum.comap`, `PrimeSpectrum.continuous_comap`, and `IsPushout`;
- `bridge/view`: the induced `TopCat` morphisms attached to `S`. -/

namespace SurjectiveRingPullbackSituation

variable (S : SurjectiveRingPullbackSituation B A A')

/-- The topological space `Spec(B')` attached to a surjective ring pullback situation. -/
abbrev specBprime : TopCat :=
  TopCat.of (PrimeSpectrum S.Bprime)

/-- The canonical map `Spec(A) → Spec(B)` induced by `B → A`. -/
abbrev specToB : TopCat.of (PrimeSpectrum A) ⟶ TopCat.of (PrimeSpectrum B) :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.toA, PrimeSpectrum.continuous_comap S.toA⟩

/-- The canonical map `Spec(A) → Spec(A')` induced by `A' → A`. -/
abbrev specToAprime : TopCat.of (PrimeSpectrum A) ⟶ TopCat.of (PrimeSpectrum A') :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.fromAprime, PrimeSpectrum.continuous_comap S.fromAprime⟩

/-- The canonical map `Spec(B) → Spec(B')` induced by `B' → B`. -/
abbrev specBToBprime : TopCat.of (PrimeSpectrum B) ⟶ S.specBprime :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.bprimeToB, PrimeSpectrum.continuous_comap S.bprimeToB⟩

/-- The canonical map `Spec(A') → Spec(B')` induced by `B' → A'`. -/
abbrev specAprimeToBprime : TopCat.of (PrimeSpectrum A') ⟶ S.specBprime :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.bprimeToAprime, PrimeSpectrum.continuous_comap S.bprimeToAprime⟩

end SurjectiveRingPullbackSituation

-- Proof sketch: let `B'` be the categorical pullback of `B → A ← A'`. The two projection maps
-- `B' → B` and `B' → A'` induce a cocone `Spec(B) ← Spec(A) → Spec(A') ⟶ Spec(B')`. The
-- textbook proof shows that the induced map from the topological pushout to `Spec(B')` is
-- bijective, separating primes according to whether they contain `ker(A' → A)`, and then proves
-- openness of this map by the localization argument using Lemma `15.5.3`.
/-- Lemma 15.6.2: in a surjective ring pullback situation, the prime spectrum of the fibre product
ring `B ×_A A'` is the pushout of `Spec(B) ← Spec(A) → Spec(A')` in the category of topological
spaces. -/
theorem spec_pullback_of_surjective_isPushout
    (S : SurjectiveRingPullbackSituation B A A') :
    IsPushout S.specToB S.specToAprime S.specBToBprime S.specAprimeToBprime := sorry

end

/-! ### Lemma_15_6_3 (from Chap15) -/
universe u

section

variable {B A A' : Type u}
variable [CommRing B] [CommRing A] [CommRing A']

/- Domain-style sampling for 15.6.3:
- primary domain: integrality of commutative-ring maps and its stability under base change;
- sampled owner declarations:
  `RingHom.IsIntegral`,
  `RingHom.isIntegral_isStableUnderBaseChange`,
  `SurjectiveRingPullbackSituation`,
  `SurjectiveRingPullbackSituation.bprimeToAprime`;
- best owner abstraction: the mathematical property is owned by `RingHom.IsIntegral`, and the
  base-change theorem is the canonical owner declaration
  `RingHom.isIntegral_isStableUnderBaseChange`; the chapter pullback situation is only a
  source-facing bridge packaging the specific fibre-product square from Situation `15.6.1`;
- primitive data at the core layer: a ring map and the proposition that it is integral;
- derived bridge API in this file: for `S : SurjectiveRingPullbackSituation B A A'`, the map
  `S.bprimeToAprime` is derived from the pullback owner data and inherits integrality from the core
  base-change theorem.

Source/core/bridge triage:
- `source-facing`: the chapter specialization to Situation `15.6.1`;
- `core/canonical`: `RingHom.IsIntegral` and `RingHom.isIntegral_isStableUnderBaseChange`;
- `bridge/view`: `SurjectiveRingPullbackSituation` and the specialized theorem below. -/

/- Lemma 15.6.3 is a chapter-level pullback instance of the canonical base-change theorem
`RingHom.isIntegral_isStableUnderBaseChange`. -/
recall RingHom.isIntegral_isStableUnderBaseChange

/-- Lemma 15.6.3: specialized bridge from Situation `15.6.1` to the canonical base-change owner.
If `B → A` is integral in a surjective ring pullback situation, then the induced projection
`B' = B ×_A A' → A'` is integral. -/
-- Proof sketch: specialize the canonical base-change owner theorem to the pullback ring from
-- Situation `15.6.1`.
theorem isIntegral_pullback_projection_of_surjective_of_isIntegral
    (S : SurjectiveRingPullbackSituation B A A') (hBA : S.toA.IsIntegral) :
    S.bprimeToAprime.IsIntegral := by
  sorry

end

/-! ### Lemma_15_6_4 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

local notation "PullbackModuleCat" =>
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

/- Domain-style sampling for Lemma 15.6.4:
- primary domain: adjunctions for module-category base change along a pullback square of
  commutative rings;
- sampled owner declarations:
  `SurjectiveRingPullbackSituation.bprimeToB`,
  `SurjectiveRingPullbackSituation.bprimeToAprime`,
  `moduleCatBaseChangeToCategoricalPullback`,
  `module_tensor_pullback_adjunction`,
  `module_tensor_pullback_adjunction_counit_isIso`;
- best owner abstraction: the specialized adjunction
  `module_tensor_pullback_adjunction S.bprimeToB S.bprimeToAprime S.comm`;
- primitive data: the surjective pullback situation `S`;
- derived API: the left-adjoint instance on the canonical base-change functor and the right-adjoint
  instance on the canonical fibre-product functor, together with the counit isomorphism of the
  composite back to the pullback category.

Source/core/bridge triage:
- `source-facing`: Lemma 15.6.4, asserting that the base-change functor attached to the surjective
  pullback square has the fibre-product module functor as right adjoint;
- `core/canonical`: `module_tensor_pullback_adjunction`;
- `bridge/view`: the specialization of that adjunction to the pullback square built from `S`.
-/

/- Lemma 15.6.4: in a surjective pullback situation, the canonical base-change functor
`Mod_{B'} → Mod_B ×[Mod_A] Mod_{A'}`
is left adjoint to the canonical fibre-product module functor
`(N, M', φ) ↦ N ×_φ M'`. This is exactly the specialized owner adjunction from
`module_tensor_pullback_adjunction`. -/
#check (module_tensor_pullback_adjunction S.bprimeToB S.bprimeToAprime S.comm :
  baseChangeFunctor ⊣ fiberProductFunctor)

/- Lemma 15.6.4: the composite from `Mod_B ×[Mod_A] Mod_{A'}` back to itself through the
fibre-product module functor and base change is canonically isomorphic to the identity functor.
This is the specialized owner-level counit isomorphism. -/
#check (module_tensor_pullback_adjunction_counit_isIso
  S.bprimeToB
  S.bprimeToAprime
  S.comm :
    IsIso
      ((module_tensor_pullback_adjunction S.bprimeToB S.bprimeToAprime S.comm).counit :
        fiberProductFunctor ⋙ baseChangeFunctor ⟶ 𝟭 PullbackModuleCat))

end

/-! ### Lemma_15_6_5 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CommRingCat

universe u

noncomputable section

section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']

-- Proof sketch: let `J = ker(B' → B)`. Then `L' ⊗[B'] B ≃ L' / J L'`, so any element of the
-- fibre product can be adjusted by something coming from `L' ⊗[B'] J` until its first component
-- vanishes. Using the identification `J ≃ ker(A' → A)` from the pullback square, the remaining
-- element lifts from `L'`, giving surjectivity of the displayed map.
/-- Lemma 15.6.5: in the situation of Lemma 15.6.4, for a `B'`-module `L'`, the canonical
adjunction unit
`L' ⟶ (L' ⊗[B'] B) ×_{L' ⊗[B'] A} (L' ⊗[B'] A')`
is surjective. -/
theorem surjectiveRingPullbackModuleAdjunctionMap_surjective
    (S : SurjectiveRingPullbackSituation B A A')
    (L' : ModuleCat S.Bprime) :
    Function.Surjective
      (((module_tensor_pullback_adjunction
        S.bprimeToB
        S.bprimeToAprime
        S.comm).unit.app L').hom) := sorry

-- Proof sketch: use the textbook example
-- `B' = k[x, y]/(xy)`, `A' = B'/(x)`, `B = B'/(y)`, `A = B'/(x, y)`, and
-- `L' = B'/(x - y)`. The class of `x` in `L'` is nonzero but maps to zero in the fibre-product
-- module, so the adjunction map fails to be injective.
/-- The canonical adjunction unit of a surjective ring pullback situation need not be injective in
general. -/
theorem surjectiveRingPullbackModuleAdjunctionMap_not_injective_in_general :
    ¬ ∀ {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
        (S : SurjectiveRingPullbackSituation B A A')
        (L' : ModuleCat S.Bprime),
        Function.Injective
          (((module_tensor_pullback_adjunction
            S.bprimeToB
            S.bprimeToAprime
            S.comm).unit.app L').hom) := sorry

end

/-! ### Lemma_15_6_6 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

local notation "PullbackModuleCat" =>
  CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)

/- Domain-style sampling for 15.6.6:
- primary domain: morphisms in the pullback category
  `Mod_B ×[Mod_A] Mod_{A'}`
  attached to Situation `15.6.1`, together with the induced map on the fibre-product module from
  `15.6.4`;
- sampled owner declarations:
  `SurjectiveRingPullbackSituation`,
  `CategoricalPullback`,
  `module_tensor_pullback_right_adjoint`,
  `Functor.map`;
- best owner abstraction: the primitive source-facing data are an object
  `X : CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)`
  and a morphism `f : X ⟶ Y`; the induced map on fibre-product modules is the derived canonical
  morphism `((module_tensor_pullback_right_adjoint
    S.bprimeToB
    S.bprimeToAprime
    S.comm).map f)`;
- primitive data: `S`, `X`, `Y`, and `f`;
- derived API: the component maps `f.fst`, `f.snd`, and the induced map on the fibre-product
  module.

Source/core/bridge triage:
- `source-facing`: `surjectiveRingPullbackModuleFiberProduct_map_surjective`;
- `core/canonical`: the functor
  `module_tensor_pullback_right_adjoint S.bprimeToB S.bprimeToAprime S.comm`;
- `bridge/view`: none; the theorem reads off surjectivity of the induced map from surjectivity of
  the component morphisms in the pullback category. -/

-- Proof sketch: view `X` and `Y` as triples `(N₁, M'₁, φ₁)` and `(N₂, M'₂, φ₂)` in the canonical
-- pullback category of `15.6.4`. The morphism `f` provides the compatible pair of maps
-- `f.fst : N₁ → N₂` and `f.snd : M'₁ → M'₂`; surjectivity of these components is exactly the
-- hypothesis of the textbook argument, which then gives surjectivity on the induced map between
-- the fibre-product modules.
/-- Lemma 15.6.6: in Situation `15.6.1`, a morphism in
`Mod_B ×[Mod_A] Mod_{A'}`
whose `B`-component and `A'`-component are surjective induces a surjective map on the associated
fibre-product modules over `B' = B ×_A A'`. -/
theorem surjectiveRingPullbackModuleFiberProduct_map_surjective
    {X Y : PullbackModuleCat}
    (f : X ⟶ Y)
    (hfst : Function.Surjective f.fst)
    (hsnd : Function.Surjective f.snd) :
    Function.Surjective
      ((module_tensor_pullback_right_adjoint
        S.bprimeToB
        S.bprimeToAprime
        S.comm).map f) := sorry

end

/-! ### Lemma_15_6_7 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CommRingCat

universe u

noncomputable section

section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']

variable (S : SurjectiveRingPullbackSituation B A A')

local notation "PullbackModuleCat" =>
  CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)

local notation "fiberProductFunctor" =>
  module_tensor_pullback_right_adjoint S.bprimeToB S.bprimeToAprime S.comm

/- Domain-style sampling for 15.6.7:
- primary domain: finiteness of modules under the canonical fibre-product functor attached to a
  surjective pullback square of commutative rings;
- sampled owner declarations:
  `SurjectiveRingPullbackSituation`,
  `CategoricalPullback`,
  `module_tensor_pullback_right_adjoint`,
  `Module.Finite`;
- best owner abstraction: the source-facing datum is an object
  `X : CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)`,
  and the fibre-product module is the derived object `fiberProductFunctor.obj X`;
- primitive data: `S` and `X`;
- derived API: the component modules `X.fst`, `X.snd`, and finiteness of the induced fibre-product
  module.

Source/core/bridge triage:
- `source-facing`: `surjectiveRingPullbackModuleFiberProduct_finite`;
- `core/canonical`: the functor
  `module_tensor_pullback_right_adjoint S.bprimeToB S.bprimeToAprime S.comm`;
- `bridge/view`: none; the theorem is stated directly for the canonical owner. -/

-- Proof sketch: choose finitely many generators of `X.fst` over `B` and of `X.snd` over `A'`.
-- Using Lemma `15.6.4`, lift the generators of `X.fst` to the fibre-product module and express
-- generators of `X.snd` via images of further elements of the fibre product. Surjectivity of
-- `B' → B` and the description of its kernel then show these lifted elements generate the whole
-- fibre-product module over `B'`.
/-- Lemma 15.6.7: in a surjective pullback situation, if `N` is finite over `B` and `M'` is
finite over `A'`, then the fibre-product module `N ×_φ M'` is finite over `B'`. -/
theorem surjectiveRingPullbackModuleFiberProduct_finite
    (X : PullbackModuleCat)
    (hfst : Module.Finite B X.fst) (hsnd : Module.Finite A' X.snd) :
    Module.Finite S.Bprime ((fiberProductFunctor).obj X) := sorry

end

/-! ### Lemma_15_6_8 (from Chap15) -/
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

/-! ### Lemma_15_6_9 (from Chap15) -/
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
