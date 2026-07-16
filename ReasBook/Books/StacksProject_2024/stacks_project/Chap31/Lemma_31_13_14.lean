import StacksProject_2024.stacks_project.Chap31.Definition_31_13_12
import StacksProject_2024.stacks_project.Chap31.Lemma_31_13_7

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {S S' : Scheme.{u}}
variable [CategoryTheory.MonoidalCategory (RingedSpace.Modules S'.toRingedSpace)]

/-
Lemma 31.13.14 (1): if the inverse-image closed subschemes `D₁.comap f` and `D₂.comap f` are
effective Cartier divisors on `S'`, then the inverse image of the sum is again an effective
Cartier divisor. Since Chapter 31 identifies the divisor sum with multiplication on
`S.IdealSheafData`, keep the source statement as a bridge to the canonical owner
`IsEffectiveCartierDivisor`.
-/

/-- Companion spelling of Lemma 31.13.14 (1) in terms of the inverse-image effective Cartier
divisor owner. -/
theorem isEffectiveCartierDivisor_comap_effectiveCartierDivisorSum
    (f : S' ⟶ S) (D₁ D₂ : S.IdealSheafData)
    (hD₁ : (D₁.comap f).IsEffectiveCartierDivisor)
    (hD₂ : (D₂.comap f).IsEffectiveCartierDivisor) :
    ((effectiveCartierDivisorSum D₁ D₂).comap f).IsEffectiveCartierDivisor := by
  sorry

/-- Lemma 31.13.14 (1): if the pullbacks of `D₁` and `D₂` along `f : S' ⟶ S` are defined, then
the pullback of their sum is defined. -/
@[stacks 01WW]
theorem pullbackDefined_effectiveCartierDivisorSum
    (f : S' ⟶ S) (D₁ D₂ : S.IdealSheafData)
    (hD₁ : pullbackDefined D₁ f)
    (hD₂ : pullbackDefined D₂ f) :
    pullbackDefined (effectiveCartierDivisorSum D₁ D₂) f := by
  rw [pullbackDefined_iff] at hD₁ hD₂ ⊢
  exact isEffectiveCartierDivisor_comap_effectiveCartierDivisorSum f D₁ D₂ hD₁ hD₂

end AlgebraicGeometry.Scheme.IdealSheafData
