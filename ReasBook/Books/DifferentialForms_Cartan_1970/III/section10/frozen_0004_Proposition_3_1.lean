import Mathlib
import cartan.III.section10.«frozen_0003_Theorem_III_4_extra_3»

-- Declarations for this item will be appended below by the statement pipeline.

open Metric

/-- A Laurent expansion on an annulus yields the corresponding holomorphic decomposition into its
nonnegative and negative powers. -/
-- Proof sketch: split the Laurent series into its nonnegative and negative-index subseries,
-- observe that these converge on the disc and exterior region respectively, and compare their sum
-- with the original Laurent expansion on the annulus.
theorem HasLaurentExpansionOnAnnulus.exists_holomorphicAnnulusDecomposition
    {ρ₂ ρ₁ : NNReal} {f : ℂ → ℂ} (hf : HasLaurentExpansionOnAnnulus f ρ₂ ρ₁) :
    ∃ f₁ f₂,
      AnalyticOnNhd ℂ f₁ (ball (0 : ℂ) ρ₁) ∧
        AnalyticOnNhd ℂ f₂ (closedBall (0 : ℂ) ρ₂)ᶜ ∧
          Set.EqOn f (fun z ↦ f₁ z + f₂ z) (complexOpenAnnulus ρ₂ ρ₁) := sorry

/-- Proposition 3.1: every holomorphic function on the annulus `ρ₂ < ‖z‖ < ρ₁` can be written as
the sum of a holomorphic function on `‖z‖ < ρ₁` and a holomorphic function on `ρ₂ < ‖z‖`. -/
-- Proof sketch: first use `AnalyticOnNhd.hasLaurentExpansionOnAnnulus` to obtain the canonical
-- Laurent expansion on `complexOpenAnnulus ρ₂ ρ₁`, then apply
-- `HasLaurentExpansionOnAnnulus.exists_holomorphicAnnulusDecomposition`.
theorem exists_holomorphic_annulus_decomposition
    {ρ₂ ρ₁ : NNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁)) :
    ∃ f₁ f₂,
      AnalyticOnNhd ℂ f₁ (ball (0 : ℂ) ρ₁) ∧
      AnalyticOnNhd ℂ f₂ (closedBall (0 : ℂ) ρ₂)ᶜ ∧
          Set.EqOn f (fun z ↦ f₁ z + f₂ z) (complexOpenAnnulus ρ₂ ρ₁) := by
  simpa using hf.hasLaurentExpansionOnAnnulus.exists_holomorphicAnnulusDecomposition
