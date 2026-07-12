import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap10.Lemma_10_99_8
import StacksProject_2024.Chap10.Remark_10_75_9
import StacksProject_2024.Chap15.Situation_15_6_1
import StacksProject_2024.Chap15.Lemma_15_5_4

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

namespace SurjectiveRingPullbackSituation

variable (S : SurjectiveRingPullbackSituation B A A')

-- Proof sketch: an element of `ker(A' → A)` determines the pullback pair `(0, a')`, so the image
-- of `ker(B' → B)` in `A'` is exactly `ker(A' → A)`.
/-- Helper for Lemma 15.6.8: the kernel ideal of `B' → B` maps onto the kernel ideal of
`A' → A`. -/
theorem kernelIdealToB_image_eq_kernelIdealInAprime :
    Ideal.map S.bprimeToAprime (RingHom.ker S.bprimeToB) = RingHom.ker S.fromAprime := by
  apply le_antisymm
  · -- Any element coming from `ker(B' → B)` has zero image in `A` by the pullback relation.
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    refine RingHom.mem_ker.mpr ?_
    rw [← show S.toA (S.bprimeToB x) = S.fromAprime (S.bprimeToAprime x) from
      congrArg (fun k ↦ k x) S.comm]
    simpa using congrArg S.toA (RingHom.mem_ker.mp hx)
  · -- For the reverse inclusion, represent `x ∈ ker(A' → A)` by the pullback point `(0, x)`.
    intro x hx
    let f : CommRingCat.of B ⟶ CommRingCat.of A := CommRingCat.ofHom S.toA
    let g : CommRingCat.of A' ⟶ CommRingCat.of A := CommRingCat.ofHom S.fromAprime
    let y : ↑(pullback f g) :=
      Concrete.pullbackMk f g (0 : B) x
        (by simpa [f, g] using (RingHom.mem_ker.mp hx).symm)
    have hy : y ∈ RingHom.ker S.bprimeToB := by
      -- The first pullback coordinate of `(0, x)` is zero by construction.
      refine RingHom.mem_ker.mpr ?_
      change pullback.fst f g y = 0
      simp [y, f, g]
    rw [← show S.bprimeToAprime y = x by
      change pullback.snd f g y = x
      simp [y, f, g]]
    exact Ideal.mem_map_of_mem S.bprimeToAprime hy

end SurjectiveRingPullbackSituation

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
        S.comm).obj L') := by
  let _ : Module.Flat S.Bprime L' := hflat
  constructor
  · -- The first pullback component is scalar extension along `B' → B`, so flatness base-changes.
    let _ : Algebra S.Bprime B := S.bprimeToB.toAlgebra
    simpa using Module.Flat.baseChange (R := S.Bprime) (S := B) (M := L')
  · -- The second pullback component is scalar extension along `B' → A'`, so the same argument
    -- applies over `A'`.
    let _ : Algebra S.Bprime A' := S.bprimeToAprime.toAlgebra
    simpa using Module.Flat.baseChange (R := S.Bprime) (S := A') (M := L')

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

/-- Helper for Lemma 15.6.8: the canonical map `B' → B × A'` is injective, so the left edge of
the source short exact row is already under control before tensoring. -/
theorem bprime_to_prod_injective :
    Function.Injective (fun x : S.Bprime ↦ (S.bprimeToB x, S.bprimeToAprime x)) := by
  intro x y hxy
  -- The pullback ring is a subtype of pairs with matching image in `A`, so equality of both
  -- projections gives equality of the underlying pair.
  apply Subtype.ext
  exact Prod.ext hxy.1 hxy.2

-- Proof sketch: argue as in the textbook with the ideal `J = ker(B' → B)` and the local
-- criterion for flatness modulo a nilpotent ideal. Flatness of `N` over `B` controls the part
-- away from `J`, while flatness of `M'` over `A'` identifies the `J`-torsion piece with an
-- injective tensor map over `A'`.
/-- Lemma 15.6.8 (1): if `(N, M', \varphi)` is a pullback triple with `N` flat over `B` and `M'`
flat over `A'`, then the fibre-product module `N ×_\varphi M'` is flat over `B' = B ×_A A'`. -/
@[stacks 0D2I]
theorem surjectiveRingPullbackModuleFiberProduct_flat
    ⦃X : PBMod⦄
    (hflat : surjectiveRingPullbackFlatPullbackProperty S X) :
    Module.Flat S.Bprime
      ((module_tensor_pullback_right_adjoint
        S.bprimeToB
        S.bprimeToAprime
        S.comm).obj X) :=
  -- Route correction: follow the source proof through the special ideal
  -- `J = RingHom.ker S.bprimeToB`, not through the adjunction-unit comparison.
  -- TODO: apply `Module.Flat.iff_lift_lsmul_comp_subtype_injective`; first quotient an arbitrary
  -- ideal by its intersection with `J` using `S.bprimeToB_surjective`, then handle the
  -- `J`-supported part by transporting `J ⊗[S.Bprime] N' → N'` to the ideal-tensor map
  -- `(RingHom.ker S.fromAprime) ⊗[A'] X.snd → X.snd`, use
  -- `tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module` to rewrite the kernel as
  -- `Tor₁`, and finally apply `tor_one_vanishes_of_annihilated_by_ideal_pow` to the
  -- `A'`-stable enlargement inside `J`.
  sorry

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
@[stacks 0D2I]
theorem surjectiveRingPullbackModuleAdjunctionMap_isIso_of_flat
    (L' : ModuleCat S.Bprime)
    (hflat : Module.Flat S.Bprime L') :
    IsIso ((module_tensor_pullback_adjunction
      S.bprimeToB
      S.bprimeToAprime
      S.comm).unit.app L') :=
  -- Route correction: use the source short-exact-row proof
  -- `0 → B' → B ⊕ A' → A → 0`, not the earlier comparison-first route.
  -- TODO: package the canonical `S.Bprime`-module row as `ShortComplex.ShortExact`, tensor it on
  -- the left by `L'`, identify the tensorized first map with the adjunction unit composed with
  -- `fiber_product_kernel_iota`, and combine flatness of `L'` with
  -- `surjectiveRingPullbackModuleAdjunctionMap_surjective` to conclude the unit is bijective.
  sorry

/-- Helper for Lemma 15.6.8: the adjunction unit is an isomorphism on the flat full subcategory.
-/
theorem surjectiveRingPullbackFlat_unit_app_isIso
    (L' : FlatModuleCat S.Bprime) :
    IsIso ((module_tensor_pullback_adjunction
      S.bprimeToB
      S.bprimeToAprime
      S.comm).unit.app L'.obj) := by
  -- Proof comment: part `(2)` is exactly the objectwise unit-isomorphism statement for flat
  -- `B'`-modules.
  exact surjectiveRingPullbackModuleAdjunctionMap_isIso_of_flat S L'.obj L'.property

/-- Helper for Lemma 15.6.8: the restricted adjunction unit component on the flat full
subcategory. -/
noncomputable abbrev surjectiveRingPullbackFlat_unitIsoApp
    (L' : FlatModuleCat S.Bprime) :
    L' ≅ ((surjectiveRingPullbackFlatModuleBaseChangeFunctor S ⋙
      surjectiveRingPullbackFlatModuleFiberProductFunctor S).obj L') :=
  letI := surjectiveRingPullbackFlat_unit_app_isIso S L'
  (flatModuleProperty S.Bprime).isoMk
    (asIso ((module_tensor_pullback_adjunction
      S.bprimeToB
      S.bprimeToAprime
      S.comm).unit.app L'.obj))

/-- Helper for Lemma 15.6.8: the restricted adjunction unit is natural on flat modules. -/
theorem surjectiveRingPullbackFlat_unitIso_naturality
    {L₁ L₂ : FlatModuleCat S.Bprime}
    (f : L₁ ⟶ L₂) :
    f ≫ (surjectiveRingPullbackFlat_unitIsoApp S L₂).hom =
      (surjectiveRingPullbackFlat_unitIsoApp S L₁).hom ≫
        ((surjectiveRingPullbackFlatModuleBaseChangeFunctor S ⋙
          surjectiveRingPullbackFlatModuleFiberProductFunctor S).map f) := by
  -- Proof comment: forget to the ambient module category and use naturality of the adjunction
  -- unit.
  ext
  simpa [surjectiveRingPullbackFlat_unitIsoApp] using
    NatTrans.naturality
      ((module_tensor_pullback_adjunction
        S.bprimeToB
        S.bprimeToAprime
        S.comm).unit) f

/-- Helper for Lemma 15.6.8: the restricted adjunction unit natural isomorphism. -/
noncomputable abbrev surjectiveRingPullbackFlat_unitIso
    :
    𝟭 (FlatModuleCat S.Bprime) ≅
      surjectiveRingPullbackFlatModuleBaseChangeFunctor S ⋙
        surjectiveRingPullbackFlatModuleFiberProductFunctor S :=
  NatIso.ofComponents
    (fun L' ↦ surjectiveRingPullbackFlat_unitIsoApp S L')
    (fun _ _ f ↦ surjectiveRingPullbackFlat_unitIso_naturality S f)

/-- Helper for Lemma 15.6.8: the ambient adjunction counit is an isomorphism on pullback triples,
hence also on the flat full subcategory. -/
theorem surjectiveRingPullbackFlat_counit_app_isIso
    (X : SurjectiveRingPullbackFlatPullbackCat S) :
    IsIso ((module_tensor_pullback_adjunction
      S.bprimeToB
      S.bprimeToAprime
      S.comm).counit.app X.obj) := by
  -- Proof comment: Lemma `15.6.4` gives the ambient counit isomorphism objectwise, and the flat
  -- full subcategory is obtained by forgetting no data from the underlying pullback object.
  letI : IsIso ((module_tensor_pullback_adjunction
    S.bprimeToB
    S.bprimeToAprime
    S.comm).counit) :=
      module_tensor_pullback_adjunction_counit_isIso
        S.bprimeToB
        S.bprimeToAprime
        S.comm
  infer_instance

/-- Helper for Lemma 15.6.8: the restricted adjunction counit component on the flat pullback full
subcategory. -/
noncomputable abbrev surjectiveRingPullbackFlat_counitIsoApp
    (X : SurjectiveRingPullbackFlatPullbackCat S) :
    ((surjectiveRingPullbackFlatModuleFiberProductFunctor S ⋙
      surjectiveRingPullbackFlatModuleBaseChangeFunctor S).obj X) ≅ X :=
  letI := surjectiveRingPullbackFlat_counit_app_isIso S X
  (surjectiveRingPullbackFlatPullbackProperty S).isoMk
    (asIso ((module_tensor_pullback_adjunction
      S.bprimeToB
      S.bprimeToAprime
      S.comm).counit.app X.obj))

/-- Helper for Lemma 15.6.8: the restricted adjunction counit is natural on the flat pullback full
subcategory. -/
theorem surjectiveRingPullbackFlat_counitIso_naturality
    {X Y : SurjectiveRingPullbackFlatPullbackCat S}
    (f : X ⟶ Y) :
    ((surjectiveRingPullbackFlatModuleFiberProductFunctor S ⋙
        surjectiveRingPullbackFlatModuleBaseChangeFunctor S).map f) ≫
        (surjectiveRingPullbackFlat_counitIsoApp S Y).hom =
      (surjectiveRingPullbackFlat_counitIsoApp S X).hom ≫ f := by
  -- Proof comment: forget to the ambient pullback category and use naturality of the adjunction
  -- counit.
  ext
  simpa [surjectiveRingPullbackFlat_counitIsoApp] using
    NatTrans.naturality
      ((module_tensor_pullback_adjunction
        S.bprimeToB
        S.bprimeToAprime
        S.comm).counit) f

/-- Helper for Lemma 15.6.8: the restricted adjunction counit natural isomorphism. -/
noncomputable abbrev surjectiveRingPullbackFlat_counitIso
    :
    surjectiveRingPullbackFlatModuleFiberProductFunctor S ⋙
        surjectiveRingPullbackFlatModuleBaseChangeFunctor S ≅
      𝟭 (SurjectiveRingPullbackFlatPullbackCat S) :=
  NatIso.ofComponents
    (fun X ↦ surjectiveRingPullbackFlat_counitIsoApp S X)
    (fun _ _ f ↦ surjectiveRingPullbackFlat_counitIso_naturality S f)

-- Proof sketch: the restricted base-change functor lands in the flat pullback full subcategory by
-- the helper theorem above, and part `(1)` gives the corresponding restricted fibre-product
-- functor. Part `(2)` supplies the unit isomorphisms, while the objectwise equalities from Lemma
-- `15.6.4` give the counit isomorphisms, so the restricted base-change functor is an equivalence.
/-- Lemma 15.6.8 (3): the category of flat `B'`-modules is equivalent to the full subcategory of
`Mod_B ×_{Mod_A} Mod_{A'}` consisting of triples `(N, M', \varphi)` with `N` flat over `B` and
`M'` flat over `A'`. -/
@[stacks 0D2I]
theorem surjectiveRingPullbackFlatModuleBaseChangeFunctor_isEquivalence
    :
    Functor.IsEquivalence (surjectiveRingPullbackFlatModuleBaseChangeFunctor S) :=
by
  -- Proof comment: use the restricted fibre-product functor as quasi-inverse and package the
  -- ambient unit/counit isomorphisms on the flat full subcategories.
  exact Functor.IsEquivalence.mk'
    (surjectiveRingPullbackFlatModuleFiberProductFunctor S)
    (surjectiveRingPullbackFlat_unitIso S)
    (surjectiveRingPullbackFlat_counitIso S)

end

end
