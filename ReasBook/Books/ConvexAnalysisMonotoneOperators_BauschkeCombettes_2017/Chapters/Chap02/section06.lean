import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_2_6 (from Chap02) -/
open MeasureTheory
open MeasureTheory.L2
open scoped MeasureTheory InnerProductSpace

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {E : Type v} [NormedAddCommGroup E]

/- Example 2.6: the textbook Bochner space `L^p((Ω,\mathcal F,\mu); E)` is the canonical mathlib
space `MeasureTheory.Lp E p μ`. -/
recall MeasureTheory.Lp

/- Example 2.6: if `E` is complete, then the canonical Bochner `L²` space
`L²((Ω,\mathcal F,\mu); E)` is complete. In particular, when `E` is a real Hilbert space, this
supplies the completeness part of the Hilbert-space structure on `L²((Ω,\mathcal F,\mu); E)`. -/
example [CompleteSpace E] : CompleteSpace (Ω →₂[μ] E) :=
  inferInstance

variable [InnerProductSpace ℝ E]

/- Example 2.6: for a real inner product space `E`, the canonical inner product on
`L²((Ω,\mathcal F,\mu); E)` is the integral of the pointwise inner product. -/
recall inner_def
