import Mathlib
import StacksProject_2024.stacks_project.Chap15.Situation_15_6_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_6_4

-- Declarations for this item will be appended below by the statement pipeline.

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
