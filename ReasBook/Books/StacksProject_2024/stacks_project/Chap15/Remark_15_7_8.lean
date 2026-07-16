import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.stacks_project.Chap15.Lemma_15_7_5

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Limits.CategoricalPullback

universe u

noncomputable section

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _

/- Domain-style sampling for Remark 15.7.8:
- primary domain: finitely presented flat quotients in module categories and their compatibility
  with the tensor-square pullback category from Situation `15.7.1`;
- sampled owner declarations:
  `Under`,
  `ObjectProperty.FullSubcategory`,
  `relativeFlatModuleProperty`,
  `relativeFlatPullbackProperty`;
- best owner abstraction: quotients of a fixed module are canonically objects of an `Under`
  category, while flatness is already owned upstream by
  `relativeFlatModuleProperty` and `relativeFlatPullbackProperty` from Lemma `15.7.5`;
- primitive data: an arrow out of `L'` in `ModuleCat Dp`, or an arrow out of
  `S.relativeModuleFunctor.obj L'` in the relative pullback category;
- derived API: the object properties cutting out surjective quotients whose targets are finitely
  presented and flat, and the equivalence between the resulting full subcategory types.

Source/core/bridge triage:
- `source-facing`: the bijection of Remark `15.7.8` between the two quotient families;
- `core/canonical`: `Under`, `ObjectProperty.FullSubcategory`, `Module.FinitePresentation`,
  `relativeFlatModuleProperty`, and `relativeFlatPullbackProperty`;
- `bridge/view`: the quotient properties below, which cut out the source-facing families inside
  the canonical `Under` owners. -/

/-- The object property on `Mod_{D'}` requiring finite presentation over `D'` together with
flatness over `B'`. -/
abbrev relativeFpFlatModuleProperty
    (S : Situation) :
    ObjectProperty (ModuleCat Dp) :=
  fun Q ↦ Module.FinitePresentation Dp Q ∧ relativeFlatModuleProperty S Q

/-- The object property on the relative pullback category requiring both components to be finitely
presented and flat over the original base rings. -/
abbrev relativeFpFlatPullbackProperty
    (S : Situation) :
    ObjectProperty S.relativeModuleCategory :=
  fun Q ↦
    Module.FinitePresentation S.D Q.fst ∧
      Module.FinitePresentation S.CPrime Q.snd ∧
        relativeFlatPullbackProperty S Q

/-- The object property on `Under L'` selecting surjective quotients of `L'` whose targets are
finitely presented over `D'` and flat over `B'`. -/
abbrev relativeFpFlatQuotientProperty
    (S : Situation) (L' : ModuleCat Dp) :
    ObjectProperty (Under L') :=
  fun Q ↦ Function.Surjective Q.hom.hom ∧ relativeFpFlatModuleProperty S Q.right

/-- The object property on the under-category of `S.relativeModuleFunctor.obj L'` selecting
compatible pairs of surjective quotients whose `D`- and `C'`-components are finitely presented and
flat over `B` and `A'`, respectively. -/
abbrev relativeFpFlatPullbackQuotientProperty
    (S : Situation) (L' : ModuleCat Dp) :
    ObjectProperty (Under (S.relativeModuleFunctor.obj L')) :=
  fun Q ↦
    let q := Q.hom
    Function.Surjective q.fst.hom ∧
      Function.Surjective q.snd.hom ∧
        relativeFpFlatPullbackProperty S Q.right

variable (S : Situation)

-- Proof sketch: send a surjective quotient `L' → Q'` to the pair of its scalar extensions to `D`
-- and `C'`, viewed as a quotient in the relative pullback category via the situation-level
-- base-change functor derived from `moduleCatBaseChangeToCategoricalPullback`.
-- For the converse, take the fibre-product module attached to a compatible quotient pair using
-- `module_tensor_pullback_right_adjoint S.dprimeToD S.dprimeToCPrime S.tensor_square_commutes`,
-- use Lemma `15.6.5` and Lemma `15.6.6` for surjectivity of
-- the comparison map, apply Lemma `15.7.5` for flatness, and deduce finite presentation from
-- Lemma `15.7.6` using the finite-presentation hypothesis on `B' → D'`.
/-- Remark 15.7.8: if `B' → D'` is finitely presented, then surjective quotients `L' → Q'` with
`Q'` finitely presented over `D'` and flat over `B'` are in bijection with compatible pairs of
surjective quotients of `L' ⊗[D'] D` and `L' ⊗[D'] C'` whose targets are finitely presented and
flat over `B` and `A'`, respectively. Here the right-hand side is expressed using the relative
pullback category of Situation `15.7.1`, which packages the common quotient over `C`. -/
theorem relativeFpFlatQuotientEquivPullbackQuotient
    (hfp : S.bprimeToDp.FinitePresentation)
    (L' : ModuleCat Dp) :
    (relativeFpFlatQuotientProperty S L').FullSubcategory ≃
      (relativeFpFlatPullbackQuotientProperty S L').FullSubcategory := sorry

end FiberProductBaseChangeSituation

end
