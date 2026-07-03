import Mathlib
import StacksProject_2024.Chap15.Situation_15_7_1
import StacksProject_2024.Chap15.Lemma_15_6_5
import StacksProject_2024.Chap15.Lemma_15_6_7

open CategoryTheory
open CategoryTheory.Limits
open CommRingCat
open scoped TensorProduct

universe u

noncomputable section

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _
variable (S : Situation)

local notation "fiberProductFunctor" =>
  (@module_tensor_pullback_right_adjoint
    S.C
    S.CPrime
    S.D
    Dp
    _ _ _ _
    S.dToC
    S.cprimeToC
    S.dprimeToD
    S.dprimeToCPrime
    S.tensor_square_commutes : S.relativeModuleCategory ⥤ ModuleCat Dp)

/- Domain-style sampling for Lemma 15.7.4:
- primary domain: module finiteness for the canonical fibre-product functor attached to the
  tensor square `D' → D`, `D' → C'`, `D → C`, `C' → C`;
- sampled owner declarations:
  `SurjectiveRingPullbackSituation`,
  `surjectiveRingPullbackModuleAdjunctionMap_surjective`,
  `surjectiveRingPullbackModuleFiberProduct_finite`,
  `Algebra.TensorProduct.map_surjective`;
- best owner abstraction: the tensor square should be handled through the owner theorem
  `surjectiveRingPullbackModuleFiberProduct_finite`, after packaging the square
  `D → C`, `C' → C` as a `SurjectiveRingPullbackSituation`;
- primitive data: the base-change situation `S`;
- derived API: the tensor-square surjective pullback situation and the canonical comparison map
  `D' → D ×_C C'`.

Source/core/bridge triage:
- `source-facing`: `relativeModuleFiberProduct_finite`;
- `core/canonical`: `surjectiveRingPullbackModuleFiberProduct_finite`;
- `bridge/view`: the tensor-square surjective pullback situation and the comparison
  `D' → D ×_C C'`. -/

private theorem cprimeToC_surjective
    (S : Situation) :
    Function.Surjective S.cprimeToC := by
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro d a
    obtain ⟨a', rfl⟩ := S.fromAprime_surjective a
    refine ⟨d ⊗ₜ[S.Bprime] a', ?_⟩
    let _ : Algebra A' A := S.fromAprime.toAlgebra
    rfl
  · intro z₁ z₂ hz₁ hz₂
    rcases hz₁ with ⟨w₁, rfl⟩
    rcases hz₂ with ⟨w₂, rfl⟩
    exact ⟨w₁ + w₂, by simp⟩

/-- The tensor square `D → C`, `C' → C` defines a surjective pullback situation whose source ring
is the canonical pullback `D ×_C C'`. -/
private def tensorPullbackSituation
    (S : Situation) :
    SurjectiveRingPullbackSituation S.D S.C S.CPrime where
  toA := S.dToC
  fromAprime := S.cprimeToC
  fromAprime_surjective := cprimeToC_surjective S

-- Proof sketch: apply Lemma `15.6.7` to the canonical surjective pullback situation attached to
-- the tensor square. The comparison map `D' → D ×_C C'` is surjective by Lemma `15.6.5` applied
-- to the original pullback square `B' → B`, `B' → A'`, `B → A`, `A' → A`, and then finiteness
-- descends along that surjection.
/-- Lemma 15.7.4: in the base-changed fibre-product situation of Lemma `15.7.2`, if `N` is finite
over `D` and `M'` is finite over `C'`, then the fibre-product module `N ×_φ M'` is finite over
`D'`. -/
theorem relativeModuleFiberProduct_finite
    (X : S.relativeModuleCategory)
    (hfst : Module.Finite S.D X.fst)
    (hsnd : Module.Finite S.CPrime X.snd) :
    Module.Finite Dp ((fiberProductFunctor).obj X) := sorry

end FiberProductBaseChangeSituation

end
