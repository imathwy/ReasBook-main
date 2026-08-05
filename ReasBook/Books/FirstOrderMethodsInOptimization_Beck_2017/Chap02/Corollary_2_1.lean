import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [TopologicalSpace E]

-- Proof sketch: compose `hf` with the continuous coercion `ℝ → EReal`, then apply
-- `Continuous.lowerSemicontinuous` to the resulting `EReal`-valued function.
/-- Corollary 2.1: a continuous real-valued function is closed, i.e. lower semicontinuous after
viewing it as an `EReal`-valued function. -/
theorem continuous_real_isClosed {f : E → ℝ} (hf : Continuous f) :
    LowerSemicontinuous (fun x ↦ (f x : EReal)) :=
  (continuous_coe_real_ereal.comp hf).lowerSemicontinuous
