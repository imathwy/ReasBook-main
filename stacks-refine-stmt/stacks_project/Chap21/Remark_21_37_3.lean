import Mathlib

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section

variable {DCMod : Type u₁} [Category.{v₁} DCMod]
variable {DDMod : Type u₂} [Category.{v₂} DDMod]
variable {DCAb : Type u₃} [Category.{v₃} DCAb]
variable {DDAb : Type u₄} [Category.{v₄} DDAb]

variable (forgetC : DCMod ⥤ DCAb) (forgetD : DDMod ⥤ DDAb)
variable (derivedLowerShriek : DCMod ⥤ DDMod) (derivedLowerShriekAb : DCAb ⥤ DDAb)

/-- Remark 21.37.3: in the setup of Lemma 21.37.2, even though the forget square for
`Lg_!` and `Lg_!^{Ab}` need not commute by an isomorphism, there is a natural transformation
from `Lg_!^{Ab} ∘ forget` to `forget ∘ Lg_!`. -/
def derivedLowerShriek_forget_comparison_exists : Prop :=
  Nonempty ((forgetC ⋙ derivedLowerShriekAb) ⟶ (derivedLowerShriek ⋙ forgetD))

/-- The comparison proposition is the existence of a natural transformation between the two
forgetful composites. -/
-- Proof sketch: unfold `derivedLowerShriek_forget_comparison_exists`.
theorem derivedLowerShriek_forget_comparison_exists_iff :
    derivedLowerShriek_forget_comparison_exists forgetC forgetD derivedLowerShriek
        derivedLowerShriekAb ↔
      Nonempty ((forgetC ⋙ derivedLowerShriekAb) ⟶ (derivedLowerShriek ⋙ forgetD)) := sorry

end
