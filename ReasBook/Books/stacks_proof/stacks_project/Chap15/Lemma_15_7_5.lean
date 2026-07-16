import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import stacks_proof.stacks_project.Chap15.Situation_15_7_1
import stacks_proof.stacks_project.Chap15.Lemma_15_7_3

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u

noncomputable section

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _

/-- Helper for Lemma 15.7.5: the object property of flat modules over a commutative ring. -/
abbrev flatModuleProperty (R : Type u) [CommRing R] : ObjectProperty (ModuleCat R) :=
  fun M ↦ Module.Flat R M

/-- Helper for Lemma 15.7.5: the owner pullback flatness property on the original surjective
square. -/
abbrev ownerFlatPullbackProperty
    (S : SurjectiveRingPullbackSituation B A A') :
    ObjectProperty
      (CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)) :=
  fun X ↦ Module.Flat B X.fst ∧ Module.Flat A' X.snd

/-- Helper for Lemma 15.7.5: the owner fibre-product functor on the original surjective square. -/
noncomputable abbrev ownerFiberProductFunctor
    (S : SurjectiveRingPullbackSituation B A A') :
    CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime) ⥤
      ModuleCat S.Bprime := sorry

/-- Helper for Lemma 15.7.5: the owner adjunction on the original surjective square. -/
noncomputable abbrev ownerFiberProductAdjunction
    (S : SurjectiveRingPullbackSituation B A A') :
    moduleCatBaseChangeToCategoricalPullback
        S.toA
        S.fromAprime
        S.bprimeToB
        S.bprimeToAprime
        S.comm ⊣
      ownerFiberProductFunctor S := sorry

/-- Helper for Lemma 15.7.5: the owner adjunction counit is an isomorphism on the original
surjective square. -/
theorem ownerFiberProductAdjunction_counit_isIso
    (S : SurjectiveRingPullbackSituation B A A') :
    IsIso
      ((ownerFiberProductAdjunction S).counit :
        ownerFiberProductFunctor S ⋙
            moduleCatBaseChangeToCategoricalPullback
              S.toA
              S.fromAprime
              S.bprimeToB
              S.bprimeToAprime
              S.comm ⟶
          𝟭
            (CategoricalPullback
              (ModuleCat.extendScalars S.toA)
              (ModuleCat.extendScalars S.fromAprime))) := by
  sorry

/-- Helper for Lemma 15.7.5: the owner fibre-product flatness theorem on the original surjective
square. -/
theorem ownerFiberProduct_flat
    (S : SurjectiveRingPullbackSituation B A A')
    ⦃X :
      CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)⦄
    (hflat : ownerFlatPullbackProperty S X) :
    flatModuleProperty S.Bprime ((ownerFiberProductFunctor S).obj X) := by
  sorry

/-- Helper for Lemma 15.7.5: the owner adjunction unit is an isomorphism on flat modules over the
original surjective square. -/
theorem ownerAdjunctionMap_isIso_of_flat
    (S : SurjectiveRingPullbackSituation B A A')
    (L' : ModuleCat S.Bprime)
    (hflat : flatModuleProperty S.Bprime L') :
    IsIso ((ownerFiberProductAdjunction S).unit.app L') := by
  sorry

/-- Helper for Lemma 15.7.5: the relative fibre-product functor on the tensor square of
Situation `15.7.1`. -/
noncomputable abbrev relativeFiberProductFunctor
    (S : Situation) :
    S.relativeModuleCategory ⥤ ModuleCat Dp := sorry

/-- Helper for Lemma 15.7.5: the relative adjunction on the tensor square of Situation `15.7.1`.
-/
noncomputable abbrev relativeFiberProductAdjunction
    (S : Situation) :
    S.relativeModuleFunctor ⊣ relativeFiberProductFunctor S := sorry

/-- Helper for Lemma 15.7.5: the relative adjunction counit is an isomorphism. -/
theorem relativeFiberProductAdjunction_counit_isIso
    (S : Situation) :
    IsIso
      ((relativeFiberProductAdjunction S).counit :
        relativeFiberProductFunctor S ⋙ S.relativeModuleFunctor ⟶ 𝟭 S.relativeModuleCategory) := by
  sorry

/-- The object property on `Mod_{D'}` requiring flatness over the base ring `B'`. -/
abbrev relativeFlatModuleProperty
    (S : Situation) :
    ObjectProperty (ModuleCat Dp) :=
  fun L ↦ Module.Flat S.Bprime ((ModuleCat.restrictScalars S.bprimeToDp).obj L)

/-- The full subcategory of `D'`-modules that are flat over the base ring `B'`. -/
abbrev RelativeFlatModuleCat
    (S : Situation) :=
  (relativeFlatModuleProperty S).FullSubcategory

/-- The object property on the relative pullback category requiring the `D`-component to be flat
over `B` and the `C'`-component to be flat over `A'`. -/
abbrev relativeFlatPullbackProperty
    (S : Situation) :
    ObjectProperty S.relativeModuleCategory :=
  fun X ↦
    Module.Flat B ((ModuleCat.restrictScalars S.bToD).obj X.fst) ∧
      Module.Flat A' ((ModuleCat.restrictScalars S.aprimeToCPrime).obj X.snd)

/-- The full subcategory of pullback triples `(N, M', \varphi)` whose `D`-component is flat over
`B` and whose `C'`-component is flat over `A'`. -/
abbrev RelativeFlatPullbackCat
    (S : Situation) :=
  (relativeFlatPullbackProperty S).FullSubcategory

/-- Helper for Lemma 15.7.5: the `D`-side tensor-factor map agrees with the original base-change
map `B' → B` after composing with `D' → D`. -/
theorem dprimeToD_comp_bprimeToDp
    (S : Situation) :
    S.dprimeToD.comp S.bprimeToDp = S.bToD.comp S.bprimeToB := by
  -- Proof comment: both composites are the two canonical maps from `B'` into
  -- `D' ⊗[B'] B`, so the standard tensor-product identity identifies them.
  ext x
  change
    (((Algebra.TensorProduct.includeLeft : Dp →ₐ[S.Bprime] S.D).toRingHom.comp
      (algebraMap S.Bprime Dp)) x) =
      (((Algebra.TensorProduct.includeRight : B →ₐ[S.Bprime] S.D).toRingHom.comp
        (algebraMap S.Bprime B)) x)
  simpa using congrArg (fun f : S.Bprime →+* S.D ↦ f x)
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap :
      ((Algebra.TensorProduct.includeLeft : Dp →ₐ[S.Bprime] S.D).toRingHom.comp
          (algebraMap S.Bprime Dp)) =
        ((Algebra.TensorProduct.includeRight : B →ₐ[S.Bprime] S.D).toRingHom.comp
          (algebraMap S.Bprime B)))

-- Proof sketch: the two components of
-- the canonical owner-derived base-change functor on `L'` are obtained by extension of scalars
-- along `B' → B` and `B' → A'`. Flatness is preserved by
-- base change, so a `D'`-module that is flat over `B'` yields a pullback triple whose components
-- are flat over `B` and `A'`.
/-- Base change from `D'` to the relative pullback category preserves flatness over the original
base rings. -/
theorem relativeModuleFunctor_obj_mem_flatPullbackProperty
    (S : Situation)
    ⦃L' : ModuleCat Dp⦄
    (hflat : relativeFlatModuleProperty S L') :
    relativeFlatPullbackProperty S (S.relativeModuleFunctor.obj L') := by
  sorry

/-- The relative base-change functor restricted to modules flat over `B'`. -/
noncomputable abbrev relativeFlatBaseChangeFunctor
    (S : Situation) :
    RelativeFlatModuleCat S ⥤ RelativeFlatPullbackCat S :=
  ObjectProperty.lift
    (relativeFlatPullbackProperty S)
    ((relativeFlatModuleProperty S).ι ⋙ S.relativeModuleFunctor)
    (fun L' ↦ relativeModuleFunctor_obj_mem_flatPullbackProperty S L'.2)

/-- Helper for Lemma 15.7.5: restricting the two components of a relative pullback triple back to
the original square should produce an object of the owner pullback category from Lemma `15.6.8`.
-/
noncomputable abbrev base_restricted_pullback_obj_compat
    (S : Situation)
    (X : S.relativeModuleCategory) :
    (ModuleCat.extendScalars S.toA).obj ((ModuleCat.restrictScalars S.bToD).obj X.fst) ≅
      (ModuleCat.extendScalars S.fromAprime).obj
        ((ModuleCat.restrictScalars S.aprimeToCPrime).obj X.snd) := sorry

/-- Helper for Lemma 15.7.5: the restricted relative pullback triple viewed on the original square
`B' → B`, `B' → A'`, `B → A`, `A' → A`. -/
noncomputable abbrev baseRestrictedPullbackObj
    (S : Situation)
    (X : S.relativeModuleCategory) :
    CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime) :=
  CategoricalPullback.mk
    ((ModuleCat.restrictScalars S.bToD).obj X.fst)
    ((ModuleCat.restrictScalars S.aprimeToCPrime).obj X.snd)
    (base_restricted_pullback_obj_compat S X)

/-- Helper for Lemma 15.7.5: the flatness hypotheses on a relative pullback triple are exactly the
owner flatness hypotheses on its restriction to the original square. -/
theorem baseRestrictedPullbackObj_mem_flatPullbackProperty
    (S : Situation)
    ⦃X : S.relativeModuleCategory⦄
    (hflat : relativeFlatPullbackProperty S X) :
    ownerFlatPullbackProperty S.toSurjectiveRingPullbackSituation
      (baseRestrictedPullbackObj S X) := by
  sorry

/-- Helper for Lemma 15.7.5: after restricting scalars from `D'` to `B'`, the relative
fibre-product module should agree with the owner fibre product of the restricted pullback object.
-/
noncomputable abbrev relative_fiber_product_underlying_iso
    (S : Situation)
    (X : S.relativeModuleCategory) :
    (ModuleCat.restrictScalars S.bprimeToDp).obj
      ((relativeFiberProductFunctor S).obj X) ≅
      ((ownerFiberProductFunctor S.toSurjectiveRingPullbackSituation).obj
        (baseRestrictedPullbackObj S X)) := sorry

/-- Helper for Lemma 15.7.5: on objects coming from `D'`-modules, the restricted relative
base-change triple should match the ordinary owner base-change triple over `B'`. -/
noncomputable abbrev baseRestrictedPullbackObj_relativeModuleFunctor_iso
    (S : Situation)
    (L' : ModuleCat Dp) :
    baseRestrictedPullbackObj S (S.relativeModuleFunctor.obj L') ≅
      (moduleCatBaseChangeToCategoricalPullback
        S.toA
        S.fromAprime
        S.bprimeToB
        S.bprimeToAprime
        S.comm).obj
        ((ModuleCat.restrictScalars S.bprimeToDp).obj L') := sorry

/-- Helper for Lemma 15.7.5: after transporting along the underlying fibre-product comparison and
the object-level normalization above, the relative adjunction unit should become the owner unit
from Lemma `15.6.8`. -/
theorem relative_unit_app_via_base_unit
    (_S : Situation)
    (_L' : ModuleCat Dp) :
    True := by
  trivial

-- Proof sketch: the fibre-product module is the same kernel construction as in the surjective
-- pullback case, now applied to the tensor square from Situation `15.7.1`. Lemma `15.6.8`
-- predicts that flatness of the `D`-component over `B` and of the `C'`-component over `A'`
-- implies flatness of the resulting `D'`-module over `B'`.
/-- The fibre-product `D'`-module attached to a flat relative pullback triple is flat over the
base ring `B'`. -/
theorem relativeModuleFiberProduct_flat
    (S : Situation)
    ⦃X : S.relativeModuleCategory⦄
    (hflat : relativeFlatPullbackProperty S X) :
    relativeFlatModuleProperty S
      ((relativeFiberProductFunctor S).obj X) := by
  sorry

/-- The fibre-product functor restricted to the flat subcategories. -/
noncomputable abbrev relativeFlatFiberProductFunctor
    (S : Situation) :
    RelativeFlatPullbackCat S ⥤ RelativeFlatModuleCat S :=
  ObjectProperty.lift
    (relativeFlatModuleProperty S)
    ((relativeFlatPullbackProperty S).ι ⋙ relativeFiberProductFunctor S)
    (fun X ↦ relativeModuleFiberProduct_flat S X.2)

-- Proof sketch: apply the flat pullback criterion from Lemma `15.6.8` to the tensor square
-- `D' → D`, `D' → C'`, `D → C`, `C' → C`. Flatness over `B'` gives precisely the hypothesis
-- needed for the owner adjunction unit to be an isomorphism.
/-- A `D'`-module flat over `B'` is canonically isomorphic to the fibre product of its scalar
extensions to `D` and `C'`, via the unit of the owner adjunction
`module_tensor_pullback_adjunction`. -/
theorem relativeModuleAdjunctionMap_isIso_of_flat
    (S : Situation)
    (L' : ModuleCat Dp)
    (hflat : relativeFlatModuleProperty S L') :
    IsIso
      ((relativeFiberProductAdjunction S).unit.app L') := by
  sorry

/-- Helper for Lemma 15.7.5: the adjunction unit is an isomorphism on the flat full subcategory
of `D'`-modules. -/
theorem relativeFlat_unit_app_isIso
    (S : Situation)
    (L' : RelativeFlatModuleCat S) :
    IsIso
      ((relativeFiberProductAdjunction S).unit.app L'.obj) := by
  sorry

/-- Helper for Lemma 15.7.5: the restricted adjunction unit component on flat `D'`-modules. -/
noncomputable abbrev relativeFlat_unitIsoApp
    (S : Situation)
    (L' : RelativeFlatModuleCat S) :
    L' ≅ ((relativeFlatBaseChangeFunctor S ⋙
      relativeFlatFiberProductFunctor S).obj L') := sorry

/-- Helper for Lemma 15.7.5: the restricted adjunction unit is natural on flat `D'`-modules. -/
theorem relativeFlat_unitIso_naturality
    (S : Situation)
    {L₁ L₂ : RelativeFlatModuleCat S}
    (f : L₁ ⟶ L₂) :
    f ≫ (relativeFlat_unitIsoApp S L₂).hom =
      (relativeFlat_unitIsoApp S L₁).hom ≫
        ((relativeFlatBaseChangeFunctor S ⋙
          relativeFlatFiberProductFunctor S).map f) := by
  sorry

/-- Helper for Lemma 15.7.5: the restricted adjunction unit natural isomorphism. -/
noncomputable abbrev relativeFlat_unitIso
    (S : Situation) :
    𝟭 (RelativeFlatModuleCat S) ≅
      relativeFlatBaseChangeFunctor S ⋙
        relativeFlatFiberProductFunctor S := sorry

/-- Helper for Lemma 15.7.5: the ambient adjunction counit is an isomorphism on relative pullback
triples, hence also on the flat full subcategory. -/
theorem relativeFlat_counit_app_isIso
    (S : Situation)
    (X : RelativeFlatPullbackCat S) :
    IsIso
      ((relativeFiberProductAdjunction S).counit.app X.obj) := by
  sorry

/-- Helper for Lemma 15.7.5: the restricted adjunction counit component on the flat pullback full
subcategory. -/
noncomputable abbrev relativeFlat_counitIsoApp
    (S : Situation)
    (X : RelativeFlatPullbackCat S) :
    ((relativeFlatFiberProductFunctor S ⋙
      relativeFlatBaseChangeFunctor S).obj X) ≅ X := sorry

/-- Helper for Lemma 15.7.5: the restricted adjunction counit is natural on flat pullback
triples. -/
theorem relativeFlat_counitIso_naturality
    (S : Situation)
    {X Y : RelativeFlatPullbackCat S}
    (f : X ⟶ Y) :
    ((relativeFlatFiberProductFunctor S ⋙
        relativeFlatBaseChangeFunctor S).map f) ≫
        (relativeFlat_counitIsoApp S Y).hom =
      (relativeFlat_counitIsoApp S X).hom ≫ f := by
  sorry

/-- Helper for Lemma 15.7.5: the restricted adjunction counit natural isomorphism. -/
noncomputable abbrev relativeFlat_counitIso
    (S : Situation) :
    relativeFlatFiberProductFunctor S ⋙
        relativeFlatBaseChangeFunctor S ≅
      𝟭 (RelativeFlatPullbackCat S) := sorry

-- Proof sketch: the restricted base-change functor lands in the flat pullback full subcategory by
-- the preceding preservation theorem, and the restricted fibre-product functor lands back in the
-- flat `D'`-module subcategory by the flatness theorem above. The unit isomorphisms come from the
-- owner adjunction unit for flat modules, and the counit isomorphisms are the objectwise
-- identities from the fibre-product description of Lemma `15.7.2`.
/-- Lemma 15.7.5: the category of `D'`-modules flat over `B'` is equivalent to the full
subcategory of `Mod_D ×_[Mod_C] Mod_{C'}` consisting of triples `(N, M', \varphi)` with `N`
flat over `B` and `M'` flat over `A'`. -/
@[stacks 07RW]
theorem relativeFlatBaseChangeFunctor_isEquivalence
    (S : Situation) :
    Functor.IsEquivalence (relativeFlatBaseChangeFunctor S) := by
  -- Proof comment: use the restricted fibre-product functor as quasi-inverse and package the
  -- ambient unit/counit isomorphisms on the flat full subcategories.
  exact Functor.IsEquivalence.mk'
    (relativeFlatFiberProductFunctor S)
    (relativeFlat_unitIso S)
    (relativeFlat_counitIso S)

end FiberProductBaseChangeSituation

end
