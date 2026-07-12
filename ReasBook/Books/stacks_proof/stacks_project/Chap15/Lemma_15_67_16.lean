import StacksProject_2024.Chap15.Lemma_15_75_12
import Mathlib.Tactic.StacksAttribute

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable {ι : Type*} [Finite ι]

/-- Lemma 15.67.16: if a finite family `f : ι → R` generates the unit ideal and each localized
derived object `K^• ⊗_R R_{f_i}` has tor-amplitude in `[a, b]`, then `K^•` already has
tor-amplitude in `[a, b]`. -/
@[stacks 066N]
theorem torAmplitudeIn_of_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hloc : ∀ i,
      HasTorAmplitudeIn (K ⊗[R]^L[Localization.Away (f i)]) a b) :
    HasTorAmplitudeIn K a b := by
  exact hasTorAmplitudeIn_of_localizationAway_unitIdeal f hunit K a b hloc

end

end CategoryTheory
