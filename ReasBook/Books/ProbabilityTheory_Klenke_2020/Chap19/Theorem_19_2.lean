import ProbabilityTheory_Klenke_2020.Chap19.Definition_19_1
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

-- Proof sketch: for each `x ∉ A`, combine the integrability of `f` and `g` under `κ x`, use
-- linearity of the integral, and substitute the harmonicity identities for `f` and `g`.
/-- Theorem 19.2: if `f` and `g` are harmonic outside `A` for a kernel `κ`, then every linear
combination `α • f + β • g` is harmonic outside `A` as well. -/
theorem IsHarmonicOutside.smul_add
    {κ : Kernel E E} {A : Set E} {f g : E → ℝ}
    (hf : IsHarmonicOutside κ A f) (hg : IsHarmonicOutside κ A g) (α β : ℝ) :
    IsHarmonicOutside κ A (α • f + β • g) := sorry

end ProbabilityTheory
