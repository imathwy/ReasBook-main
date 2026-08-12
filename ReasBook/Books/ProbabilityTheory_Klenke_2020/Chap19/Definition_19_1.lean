import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_43
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

/-- Definition 19.1: a real-valued function is harmonic on `E \ A` for a kernel `p` if at every
state outside `A` the kernel average `p f` exists and equals the original value of the function. -/
def IsHarmonicOutside (p : Kernel E E) (A : Set E) (f : E → ℝ) : Prop :=
  ∀ ⦃x : E⦄, x ∉ A → Integrable f (p x) ∧ f x = ∫ y, f y ∂p x

-- Proof sketch: if `f` is globally harmonic for `p`, then the defining integrability and
-- fixed-point identity from `IsHarmonic` hold at every state, hence in particular at each
-- `x ∉ A`.
/-- A globally harmonic function is harmonic outside every subset. -/
theorem IsHarmonic.isHarmonicOutside {p : Kernel E E} {f : E → ℝ}
    (h : IsHarmonic p f) (A : Set E) :
    IsHarmonicOutside p A f := by
  intro x hx
  exact ⟨h.1 x, h.2 x⟩

end ProbabilityTheory
