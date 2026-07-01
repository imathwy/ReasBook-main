import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/- Definition 1.43 is recall-only: the bidual space `E**` is not a new owner abstraction. It is
the iterated canonical dual type `Module.Dual ℝ (Module.Dual ℝ E)`. -/
#check (Module.Dual ℝ (Module.Dual ℝ E))

end
