import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_20 (from Chap12) -/
universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-- Definition 12.20: the Moreau envelope of parameter `γ ∈ ℝ_{++}` is the infimal convolution
of `f` with the quadratic kernel `x ↦ (1 / (2γ)) ‖x‖^2`. The source-facing Lean notation is
`{}^[γ] f`. -/
noncomputable abbrev moreauEnvelope {α : Type*} [CoeTC α EReal] (f : H → α)
    (γ : Set.Ioi (0 : ℝ)) :
    H → EReal :=
  f □ moreauQuadraticKernel γ

notation:max "{}^[" γ:max "]" f:max => ERealFunction.moreauEnvelope f γ

/-- The Moreau envelope is computed by infimizing the translated sums
`f y + (1 / (2γ)) ‖x - y‖^2`. -/
-- Proof sketch: unfold `moreauEnvelope`, expand the defining formula for `infimalConvolution`,
-- and rewrite the kernel term with `moreauQuadraticKernel_apply`.
theorem moreauEnvelope_apply {α : Type*} [CoeTC α EReal] (f : H → α)
    (γ : Set.Ioi (0 : ℝ)) (x : H) :
    ({}^[γ] f) x =
      ⨅ y : H, (f y : EReal) + ((((1 / (2 * (γ : ℝ))) * ‖x - y‖ ^ 2 : ℝ) : EReal)) := by
  simp [moreauEnvelope, infimalConvolution_apply]

end ERealFunction

/-! ### Definition_12_20_Core (from Chap12) -/
universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-- The quadratic kernel `x ↦ (1 / (2γ)) ‖x‖^2` used in the definition of the Moreau envelope. -/
noncomputable def moreauQuadraticKernel (γ : Set.Ioi (0 : ℝ)) : H → Set.Ioi (⊥ : EReal) :=
  (fun x : H ↦ (1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2).toEReal

/-- Coercing the Moreau quadratic kernel to `EReal` recovers the function
`x ↦ (1 / (2γ)) ‖x‖^2`. -/
@[simp]
theorem moreauQuadraticKernel_apply (γ : Set.Ioi (0 : ℝ)) (x : H) :
    (moreauQuadraticKernel γ x : EReal) = (((1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2 : ℝ) : EReal) := by
  simp [moreauQuadraticKernel]

/-- The quadratic function `x ↦ ‖x‖² / 2`, viewed as a positive extended-real-valued function. -/
noncomputable abbrev halfSquaredNorm : H → Set.Ioi (⊥ : EReal) :=
  moreauQuadraticKernel ⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩

/-- Coercing `halfSquaredNorm` to `EReal` recovers the quadratic function `x ↦ ‖x‖² / 2`. -/
@[simp] theorem halfSquaredNorm_apply (x : H) :
    (halfSquaredNorm x : EReal) = ((((‖x‖ ^ 2) / 2 : ℝ) : EReal)) := sorry

end ERealFunction
