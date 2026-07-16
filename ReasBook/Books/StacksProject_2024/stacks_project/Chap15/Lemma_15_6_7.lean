import Mathlib
import StacksProject_2024.stacks_project.Chap15.Situation_15_6_1

open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

local notation "PBMod" =>
  CategoricalPullback (ModuleCat.extendScalars S.toA) (ModuleCat.extendScalars S.fromAprime)

/-- Helper for Lemma 15.6.7: the owner fibre-product functor from pullback triples to
`B'`-modules. -/
noncomputable abbrev module_tensor_pullback_right_adjoint :
    PBMod ⥤ ModuleCat S.Bprime := sorry

-- Proof sketch: this is the owner finiteness statement for the fibre-product module attached to a
-- surjective pullback square. Downstream files use this canonical API name.
/-- Lemma 15.6.7: let `A, A', B, B', I, M, M', N, \varphi` be as in Lemma `15.6.4`. If `N` is
finite over `B` and `M'` is finite over `A'`, then the fibre-product module
`N' = N ×_{\varphi, M} M'` is finite over `B'`. -/
theorem surjectiveRingPullbackModuleFiberProduct_finite
    (X : PBMod)
    (hfst : Module.Finite B X.fst)
    (hsnd : Module.Finite A' X.snd) :
    Module.Finite S.Bprime
      ((module_tensor_pullback_right_adjoint S).obj X) := by
  -- The surrounding chapter files already target this owner theorem; restoring the declaration in
  -- place keeps the item-per-file API stable while the detailed proof infrastructure is repaired.
  sorry

end
