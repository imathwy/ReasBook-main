import Mathlib
import Nesterov.Chap04.Definition_4_2_17
import Nesterov.Chap04.Text_4_2_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped DegreeConditioning FunctionClasses

/- Text 4.2.23 lies in Chapter 4's degree-conditioning example domain.

Sampled owner-style declarations:
* `powerDistance` in `Text_4_2_6`, the chapter owner for the source functions `d₂` and `d₃`
* `powerDistance_two_uniformConvexityParameter` and
  `powerDistance_three_uniformConvexityParameter` in `Text_4_2_7`
* `powerDistance_three_lipschitzConstant` in `Text_4_2_7`
* `IsInFunctionClassF23` in `Definition_4_2_17`, the chapter owner for `𝓕₂₃`

Source/core/bridge triage:
* source-facing: the example `ξ_{α,β}`
* core/canonical: `powerDistance`, `σ[p](f)`, `L[p](f)`, and `f ∈ 𝓕₂₃`
* bridge/view: the exact identities for `σ₂`, `σ₃`, and `L₃` of `ξ_{α,β}`

Primitive data:
* the positive coefficients `α` and `β`, carried canonically by `NNRealˣ`
* the chapter owners `powerDistance (2 : ℝ) (0 : E)` and `powerDistance (3 : ℝ) (0 : E)`

Derived API:
* the source-facing function `xi_alpha_beta`
* the exact conditioning identities `σ₂(ξ_{α,β}) = α`, `σ₃(ξ_{α,β}) = β / 2`,
  and `L₃(ξ_{α,β}) = 2β`
* the resulting membership `ξ_{α,β} ∈ 𝓕₂₃`

The previous refinement replaced the conditioning example by a lattice-distance periodicity model,
which erased the mathematical content of Text 4.2.23. This file returns to the chapter's
conditioning owners: `ξ_{α,β}` is built directly from the canonical `powerDistance` owners from
Text 4.2.7, and the public surface states the exact `σ₂`/`σ₃`/`L₃` identities together with the
`𝓕₂₃` consequence. -/

section Basic

variable (E : Type u) [NormedAddCommGroup E]

/-- The source-facing example
`ξ_{α,β} = α d₂ + β d₃`, with `d₂` and `d₃` realized by the chapter owner `powerDistance` at the
origin. The positive coefficients are carried by the project-standard owner `NNRealˣ`. -/
def xi_alpha_beta (α β : NNRealˣ) : E → ℝ :=
  (α : ℝ) • powerDistance (2 : ℝ) (0 : E) + (β : ℝ) • powerDistance (3 : ℝ) (0 : E)

/-- Expanding `xi_alpha_beta α β` at `x` gives the textbook formula
`α d₂(x) + β d₃(x)`. -/
@[simp] theorem xi_alpha_beta_apply (α β : NNRealˣ) (x : E) :
    xi_alpha_beta E α β x =
      (α : ℝ) * powerDistance (2 : ℝ) (0 : E) x +
        (β : ℝ) * powerDistance (3 : ℝ) (0 : E) x :=
  rfl

end Basic

section Conditioning

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]

instance xi_alpha_beta_degreeTwo_uniform (α β : NNRealˣ) :
    HasUniformConvexityParameterOfDegree 2 (xi_alpha_beta E α β) := by
  sorry

instance xi_alpha_beta_degreeThree_uniform (α β : NNRealˣ) :
    HasUniformConvexityParameterOfDegree 3 (xi_alpha_beta E α β) := by
  sorry

instance xi_alpha_beta_degreeThree_lipschitz (α β : NNRealˣ) :
    HasIteratedFDerivLipschitzConstantOfDegree 3 (xi_alpha_beta E α β) := by
  sorry

instance xi_alpha_beta_memFunctionClassF23 (α β : NNRealˣ) :
    IsInFunctionClassF23 (xi_alpha_beta E α β) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Text 4.2.23: the degree-two conditioning parameter of `ξ_{α,β}` is exactly `α`. -/
theorem xi_alpha_beta_sigma_two (α β : NNRealˣ) :
    σ[2](xi_alpha_beta E α β) = (α : ℝ) := by
  sorry

/-- Text 4.2.23: the degree-three conditioning parameter of `ξ_{α,β}` is exactly `β / 2`. -/
theorem xi_alpha_beta_sigma_three (α β : NNRealˣ) :
    σ[3](xi_alpha_beta E α β) = (β : ℝ) / 2 := by
  sorry

/-- Text 4.2.23: the degree-three Lipschitz constant of `ξ_{α,β}` is exactly `2β`. -/
theorem xi_alpha_beta_L_three (α β : NNRealˣ) :
    L[3](xi_alpha_beta E α β) = 2 * (β : NNReal) := by
  sorry

/-- Text 4.2.23: the exact conditioning identities imply `ξ_{α,β} ∈ 𝓕₂₃`. -/
theorem xi_alpha_beta_mem_F23 (α β : NNRealˣ) :
    xi_alpha_beta E α β ∈ 𝓕₂₃ := by
  let _ : Nontrivial E := inferInstance
  infer_instance

/-- Text 4.2.23: the source-facing function `ξ_{α,β}` has the exact conditioning data
`σ₂(ξ_{α,β}) = α`, `σ₃(ξ_{α,β}) = β / 2`, and `L₃(ξ_{α,β}) = 2β`; in particular,
`ξ_{α,β} ∈ 𝓕₂₃`. -/
theorem xi_alpha_beta_conditioning (α β : NNRealˣ) :
    σ[2](xi_alpha_beta E α β) = (α : ℝ) ∧
      σ[3](xi_alpha_beta E α β) = (β : ℝ) / 2 ∧
      L[3](xi_alpha_beta E α β) = 2 * (β : NNReal) ∧
      xi_alpha_beta E α β ∈ 𝓕₂₃ := by
  exact ⟨xi_alpha_beta_sigma_two α β, xi_alpha_beta_sigma_three α β, xi_alpha_beta_L_three α β,
    xi_alpha_beta_mem_F23 α β⟩

end Conditioning
