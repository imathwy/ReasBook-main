import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap13.Example_13_2

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

noncomputable section

private theorem negativeFermiDiracEntropy_ne_bot (ξ : ℝ) :
    negativeFermiDiracEntropy ξ ≠ ⊥ := by
  by_cases hξ : 0 < ξ ∧ ξ < 1
  · rw [negativeFermiDiracEntropy, if_pos hξ]
    exact EReal.coe_ne_bot _
  · by_cases hx01 : ξ = 0 ∨ ξ = 1
    · rw [negativeFermiDiracEntropy, if_neg hξ, if_pos hx01]
      simp
    · rw [negativeFermiDiracEntropy, if_neg hξ, if_neg hx01]
      simp

private theorem negativeFermiDiracEntropy_minus_half_sq_isProper :
    IsProper
      (fun ξ : ℝ ↦
        negativeFermiDiracEntropy ξ +
          ((-(1 / 2 : ℝ) * ξ ^ (2 : ℕ) : ℝ) : EReal)) := by
  refine ⟨?_, ?_⟩
  · intro ξ
    exact EReal.add_ne_bot_iff.2 ⟨negativeFermiDiracEntropy_ne_bot ξ, EReal.coe_ne_bot _⟩
  · refine ⟨0, ?_⟩
    simp [dom, negativeFermiDiracEntropy]

/-- The `]-∞,+∞]`-valued tilt of the Chapter 13 negative Fermi--Dirac entropy by
`ξ ↦ -ξ² / 2`. -/
def negativeFermiDiracEntropy_minus_half_sq : ℝ → Set.Ioi (⊥ : EReal) :=
  properIoi
    (fun ξ : ℝ ↦
      negativeFermiDiracEntropy ξ +
        ((-(1 / 2 : ℝ) * ξ ^ (2 : ℕ) : ℝ) : EReal))
    negativeFermiDiracEntropy_minus_half_sq_isProper

/-- Coercing `negativeFermiDiracEntropy_minus_half_sq` back to `EReal` recovers the tilted
negative Fermi--Dirac entropy. -/
@[simp] theorem negativeFermiDiracEntropy_minus_half_sq_apply (ξ : ℝ) :
    (negativeFermiDiracEntropy_minus_half_sq ξ : EReal) =
      negativeFermiDiracEntropy ξ +
        ((-(1 / 2 : ℝ) * ξ ^ (2 : ℕ) : ℝ) : EReal) :=
  rfl

/-- The negative Fermi--Dirac entropy tilt from Example 24.46 belongs to `Γ₀(ℝ)`. -/
theorem negativeFermiDiracEntropy_minus_half_sq_mem_gammaZero :
    negativeFermiDiracEntropy_minus_half_sq ∈ Γ₀(ℝ) := by
  simpa [negativeFermiDiracEntropy_minus_half_sq] using
    (show
        properIoi
            (fun ξ : ℝ ↦
              negativeFermiDiracEntropy ξ +
                ((-(1 / 2 : ℝ) * ξ ^ (2 : ℕ) : ℝ) : EReal))
            negativeFermiDiracEntropy_minus_half_sq_isProper ∈
          Γ₀(ℝ) from
      by
        sorry)

/-- Example 24.46: the proximity operator of the negative Fermi--Dirac entropy tilt is the
canonical sigmoid function `Real.sigmoid`. -/
theorem prox_negativeFermiDiracEntropy_minus_half_sq_eq_sigmoid
    (hγ : negativeFermiDiracEntropy_minus_half_sq ∈ Γ₀(ℝ)) :
    Prox[negativeFermiDiracEntropy_minus_half_sq, hγ] = Real.sigmoid := by
  sorry

/-- Example 24.46: equivalently, the proximity operator of the negative Fermi--Dirac entropy tilt
is the textbook logistic cumulative function `ξ ↦ 1 / (1 + exp (-ξ))`. -/
theorem prox_negativeFermiDiracEntropy_minus_half_sq_eq_logistic_cdf
    (hγ : negativeFermiDiracEntropy_minus_half_sq ∈ Γ₀(ℝ)) :
    Prox[negativeFermiDiracEntropy_minus_half_sq, hγ] =
      fun ξ : ℝ ↦ 1 / (1 + Real.exp (-ξ)) := by
  simpa [Real.sigmoid_def] using prox_negativeFermiDiracEntropy_minus_half_sq_eq_sigmoid hγ

end

end ERealFunction
