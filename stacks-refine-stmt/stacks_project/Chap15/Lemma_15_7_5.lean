import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import stacks_project.Chap15.Situation_15_7_1
import stacks_project.Chap15.Lemma_15_7_2

open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _

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
    relativeFlatPullbackProperty S (S.relativeModuleFunctor.obj L') := sorry

/-- The relative base-change functor restricted to modules flat over `B'`. -/
noncomputable abbrev relativeFlatBaseChangeFunctor
    (S : Situation) :
    RelativeFlatModuleCat S ⥤ RelativeFlatPullbackCat S :=
  ObjectProperty.lift
    (relativeFlatPullbackProperty S)
    ((relativeFlatModuleProperty S).ι ⋙ S.relativeModuleFunctor)
    (fun L' ↦ relativeModuleFunctor_obj_mem_flatPullbackProperty S L'.2)

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
      ((module_tensor_pullback_right_adjoint
        S.dprimeToD
        S.dprimeToCPrime
        S.tensor_square_commutes).obj X) := sorry

/-- The fibre-product functor restricted to the flat subcategories. -/
noncomputable abbrev relativeFlatFiberProductFunctor
    (S : Situation) :
    RelativeFlatPullbackCat S ⥤ RelativeFlatModuleCat S :=
  ObjectProperty.lift
    (relativeFlatModuleProperty S)
    ((relativeFlatPullbackProperty S).ι ⋙
      module_tensor_pullback_right_adjoint
        S.dprimeToD
        S.dprimeToCPrime
        S.tensor_square_commutes)
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
      ((module_tensor_pullback_adjunction
        S.dprimeToD
        S.dprimeToCPrime
        S.tensor_square_commutes).unit.app L') := sorry

-- Proof sketch: the restricted base-change functor lands in the flat pullback full subcategory by
-- the preceding preservation theorem, and the restricted fibre-product functor lands back in the
-- flat `D'`-module subcategory by the flatness theorem above. The unit isomorphisms come from the
-- owner adjunction unit for flat modules, and the counit isomorphisms are the objectwise
-- identities from the fibre-product description of Lemma `15.7.2`.
/-- Lemma 15.7.5: the category of `D'`-modules flat over `B'` is equivalent to the full
subcategory of `Mod_D ×_[Mod_C] Mod_{C'}` consisting of triples `(N, M', \varphi)` with `N`
flat over `B` and `M'` flat over `A'`. -/
theorem relativeFlatBaseChangeFunctor_isEquivalence
    (S : Situation) :
    Functor.IsEquivalence (relativeFlatBaseChangeFunctor S) := sorry

end FiberProductBaseChangeSituation

end
