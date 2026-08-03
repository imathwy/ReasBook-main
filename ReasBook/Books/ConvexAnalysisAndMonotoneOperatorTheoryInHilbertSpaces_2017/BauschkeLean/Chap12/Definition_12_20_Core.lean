import Mathlib
import BauschkeLean.Chap09.Example_9_36

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-- The quadratic kernel `x ↦ (1 / (2γ)) ‖x‖^2` used in the definition
of the Moreau envelope. -/
noncomputable def moreauQuadraticKernel (γ : Set.Ioi (0 : ℝ)) : H → Set.Ioi (⊥ : EReal) :=
  (fun x : H ↦ (1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2).toEReal

/-- Coercing the Moreau quadratic kernel to `EReal` recovers the function
`x ↦ (1 / (2γ)) ‖x‖^2`. -/
@[simp]
theorem moreauQuadraticKernel_apply (γ : Set.Ioi (0 : ℝ)) (x : H) :
    (moreauQuadraticKernel γ x : EReal) =
      (((1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2 : ℝ) : EReal) := by
  simp [moreauQuadraticKernel]

/-- The quadratic function `x ↦ ‖x‖² / 2`, viewed as a positive
extended-real-valued function. -/
noncomputable abbrev halfSquaredNorm : H → Set.Ioi (⊥ : EReal) :=
  moreauQuadraticKernel ⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩

/-- Helper for Definition 12 20 Core: `halfSquaredNorm` is the Moreau quadratic kernel evaluated
at `γ = 1`, after coercing to `EReal`. -/
lemma moreau_quadratic_kernel_one_apply (x : H) :
    (halfSquaredNorm x : EReal) =
      ((((1 / (2 * (1 : ℝ))) * ‖x‖ ^ 2 : ℝ) : EReal)) := by
  -- Unfold the abbreviation only far enough to invoke the canonical kernel-evaluation lemma.
  rw [halfSquaredNorm, moreauQuadraticKernel_apply]

/-- Helper for Definition 12 20 Core: at `γ = 1`, the Moreau-kernel coefficient is `1 / 2`. -/
lemma moreau_kernel_at_one_coefficient (x : H) :
    ((1 / (2 * (1 : ℝ))) * ‖x‖ ^ 2 : ℝ) = (‖x‖ ^ 2) / 2 := by
  -- Normalize the scalar coefficient before comparing the two quadratic expressions.
  ring

/-- Helper for Definition 12 20 Core: the `γ = 1` coefficient normalization is preserved by the
canonical cast from `ℝ` to `EReal`. -/
lemma half_squared_norm_cast_at_one (x : H) :
    ((((1 / (2 * (1 : ℝ))) * ‖x‖ ^ 2 : ℝ) : EReal)) =
      ((((‖x‖ ^ 2) / 2 : ℝ) : EReal)) := by
  -- Transport the real-valued normalization lemma through the `EReal` coercion.
  exact congrArg (fun t : ℝ ↦ (t : EReal)) (moreau_kernel_at_one_coefficient x)

/-- Definition 12 20 Core: coercing `halfSquaredNorm` to `EReal` recovers the quadratic function
`x ↦ ‖x‖² / 2`. -/
theorem halfSquaredNorm_apply (x : H) :
    (halfSquaredNorm x : EReal) = ((((‖x‖ ^ 2) / 2 : ℝ) : EReal)) := by
  -- Route correction: first isolate the `γ = 1` kernel evaluation, then normalize the coefficient.
  calc
    (halfSquaredNorm x : EReal) =
        ((((1 / (2 * (1 : ℝ))) * ‖x‖ ^ 2 : ℝ) : EReal)) :=
      moreau_quadratic_kernel_one_apply x
    _ = ((((‖x‖ ^ 2) / 2 : ℝ) : EReal)) :=
      half_squared_norm_cast_at_one x

attribute [simp] halfSquaredNorm_apply

end ERealFunction
