import Mathlib
import StacksProject_2024.Chap15.Lemma_15_6_8

open CategoryTheory
open CategoryTheory.Limits
open CommRingCat

universe u

noncomputable section

section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']

/-- Helper for Lemma 15.16.1: the Chapter 15 fibre-product flatness theorem, re-exported under a
fresh theorem-local name so this item can keep the source pullback route without importing the
source owner directly in the target file. -/
theorem module_tensor_pullback_right_adjoint_flat_of_flat_components
    (S : SurjectiveRingPullbackSituation B A A')
    {X :
      CategoricalPullback
        (ModuleCat.extendScalars S.toA)
        (ModuleCat.extendScalars S.fromAprime)}
    (hflatB : Module.Flat B X.fst)
    (hflatAprime : Module.Flat A' X.snd) :
    Module.Flat S.Bprime
      ((module_tensor_pullback_right_adjoint
        S.bprimeToB
        S.bprimeToAprime
        S.comm).obj X) := by
  -- Route correction: reuse the compiled Chapter 15 owner theorem under a fresh local bridge
  -- name, rather than reproving the fibre-product flatness step inside the target file.
  exact surjectiveRingPullbackModuleFiberProduct_flat S ⟨hflatB, hflatAprime⟩

/-- Helper for Lemma 15.16.1: the Chapter 15 adjunction-unit surjectivity theorem, re-exported
under a fresh theorem-local name for the same pullback route. -/
theorem module_tensor_pullback_adjunction_unit_surjective
    (S : SurjectiveRingPullbackSituation B A A')
    (L' : ModuleCat S.Bprime) :
    Function.Surjective
      (((module_tensor_pullback_adjunction
        S.bprimeToB
        S.bprimeToAprime
        S.comm).unit.app L').hom) := by
  -- Reuse the canonical owner theorem once, then keep later quotient-specific transport local to
  -- Lemma 15.16.1.
  exact surjectiveRingPullbackModuleAdjunctionMap_surjective S L'

end
