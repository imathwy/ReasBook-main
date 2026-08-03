import BauschkeLean.Chap14.Example_14_5
import BauschkeLean.Chap24.Proposition_24_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

noncomputable section

-- Source/core/bridge triage:
-- - `source-facing`: Example 24.9 studies the generalized Huber radial profile on `H`.
-- - `core/canonical`: the scalar owner is `huberFunction ρ`, together with the proximal owners
--   `Prox[γ, f, hf]`.
-- - `bridge/view`: `generalized_huber_function` is the radial lift of `huberFunction ρ`, and
--   `generalized_huber_function_asEReal_eq_moreauEnvelope_scaledNorm` identifies it with the
--   Chapter 14 unit Moreau envelope of `scaledNormKernelOfPos ρ`.

section Basic

variable {H : Type u} [NormedAddCommGroup H]

/-- The generalized Huber function with threshold `ρ ∈ ℝ_{++}` is the radial lift
`x ↦ huberFunction ρ ‖x‖`. -/
noncomputable abbrev generalized_huber_function (ρ : PosReal) :
    H → Set.Ioi (⊥ : EReal) :=
  (huberFunction ρ ∘ (norm : H → ℝ)).toEReal

/-- Evaluating the generalized Huber function recovers the radial piecewise formula from
Example 24.9. -/
@[simp] theorem generalized_huber_function_apply (ρ : PosReal) (x : H) :
    (generalized_huber_function ρ x : EReal) =
      if (ρ : ℝ) < ‖x‖ then
        (((ρ : ℝ) * ‖x‖ - (ρ : ℝ) ^ 2 / 2 : ℝ) : EReal)
      else
        (((‖x‖ ^ 2 / 2 : ℝ) : EReal)) := by
  by_cases hx : (ρ : ℝ) < ‖x‖
  · have hx' : (ρ : ℝ) < |‖x‖| := by
      simpa [abs_of_nonneg (norm_nonneg x)] using hx
    simp [generalized_huber_function, Function.comp_def, hx, huberFunction_eq_of_lt ρ hx']
  · have hx' : |‖x‖| ≤ (ρ : ℝ) := by
      simpa [abs_of_nonneg (norm_nonneg x)] using le_of_not_gt hx
    simp [generalized_huber_function, Function.comp_def, hx, huberFunction_eq_of_le ρ hx']

end Basic

section Moreau

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The generalized Huber function is the unit Moreau envelope of the scaled norm kernel
`scaledNormKernelOfPos ρ`. -/
theorem generalized_huber_function_asEReal_eq_moreauEnvelope_scaledNorm (ρ : PosReal) :
    (generalized_huber_function ρ).asEReal =
      {}^[⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩]
        ((scaledNormKernelOfPos ρ : H → Set.Ioi (⊥ : EReal))) := by
  symm
  simpa [generalized_huber_function, Function.comp_def] using
    (moreauEnvelope_scaledNorm_eq_huberFunction_comp_norm ρ :
      {}^[⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩]
          ((scaledNormKernelOfPos ρ : H → Set.Ioi (⊥ : EReal))) =
        (huberFunction ρ ∘ (norm : H → ℝ)).toEReal.asEReal)

end Moreau

section Proximity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The generalized Huber function belongs to `Γ₀(H)`. -/
theorem generalized_huber_function_mem_gammaZero (ρ : PosReal) :
    generalized_huber_function ρ ∈ Γ₀(H) := sorry

/-- Example 24.9: if `f` is the generalized Huber function with threshold `ρ ∈ ℝ_{++}`, then
for every `x ∈ H`,
`Prox_(γ f) x = (1 - γρ / ‖x‖) x` when `‖x‖ > (γ + 1)ρ`, while
`Prox_(γ f) x = (γ + 1)⁻¹ x` when `‖x‖ ≤ (γ + 1)ρ`. -/
theorem prox_generalized_huber_function_eq_piecewise
    (ρ γ : PosReal) (x : H) :
    Prox[γ, generalized_huber_function ρ, generalized_huber_function_mem_gammaZero ρ] x =
      if ((γ : ℝ) + 1) * (ρ : ℝ) < ‖x‖ then
        (1 - ((γ : ℝ) * (ρ : ℝ)) / ‖x‖) • x
      else
        ((γ : ℝ) + 1)⁻¹ • x := sorry

end Proximity

end

end ERealFunction
