import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.RingTheory.Ideal.Quotient.Operations

open CategoryTheory Opposite

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{u} C]
variable {Λ : Type v} [CommRing Λ]
variable (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{v} Λ)]

/-- The `n`th quotient `Λ / I^n`, viewed as an object of `ModuleCat Λ`. -/
abbrev idealPowerQuotientSequence (I : Ideal Λ) (n : ℕ) : ModuleCat.{v} Λ :=
  ModuleCat.of Λ (Λ ⧸ I ^ n)

/-- The transition map `Λ / I^(n + 1) → Λ / I^n` in the `I`-adic quotient tower. -/
abbrev idealPowerQuotientTransition (I : Ideal Λ) (n : ℕ) :
    idealPowerQuotientSequence I (n + 1) ⟶ idealPowerQuotientSequence I n :=
  ModuleCat.ofHom
    (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (Nat.le_succ n))).toLinearMap

/-- The inverse system `n ↦ Λ / I^n` in `ModuleCat Λ`. -/
abbrev idealPowerQuotientSystem (I : Ideal Λ) : ℕᵒᵖ ⥤ ModuleCat.{v} Λ :=
  Functor.ofOpSequence (idealPowerQuotientTransition I)

/-- The inverse system of constant sheaves with values `Λ / I^n`. -/
abbrev constantIdealPowerQuotientSheafSystem
    (I : Ideal Λ) :
    ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{v} Λ) :=
  idealPowerQuotientSystem I ⋙ constantSheaf J (ModuleCat.{v} Λ)

/-- The constant sheaf with value `Λ / I`. -/
abbrev constantIdealQuotientSheaf
    (I : Ideal Λ) :
    Sheaf J (ModuleCat.{v} Λ) :=
  (constantIdealPowerQuotientSheafSystem J I).obj (op 1)

end CategoryTheory
