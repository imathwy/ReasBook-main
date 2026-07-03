import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_16 (from Items/Chap04) -/
open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/- Definition 4.16: The textbook quantity `‖f‖_p` for `p ∈ [1, ∞]` is formalized by
`MeasureTheory.eLpNorm f p μ`; for `1 ≤ p < ∞` this is the lower-integral expression
`(∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)`, and for `p = ∞` it specializes to the
essential supremum seminorm. -/
recall MeasureTheory.eLpNorm

/- For exponents `p ≠ 0, ∞`, the `ℒp` seminorm is given by the lower-integral formula from the
textbook definition. -/
recall MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal

/- At exponent `∞`, the `ℒ∞` seminorm is the essential supremum seminorm. -/
recall MeasureTheory.eLpNorm_exponent_top

/- The essential supremum is the infimum of the almost-everywhere upper bounds, matching the
textbook formula for `‖f‖_∞`. -/
recall essSup_eq_sInf

/- The textbook space `𝓛^p(μ)` of measurable functions with finite `p`-seminorm is formalized by
the predicate `MeasureTheory.MemLp f p μ`. -/
recall MeasureTheory.MemLp
