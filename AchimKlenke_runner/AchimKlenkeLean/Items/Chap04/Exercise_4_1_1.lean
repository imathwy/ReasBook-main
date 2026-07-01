import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable (hμ :
  ∃ a : NNReal,
    0 < a ∧ ∀ ⦃A : Set Ω⦄, MeasurableSet A → μ A ≠ 0 → (a : ENNReal) ≤ μ A)

include hμ

-- Proof sketch: use the hypothesis that every nonnull measurable set has measure bounded below by
-- a fixed positive constant to control the size of the level sets of `|f|`; this turns the
-- `ℒ^{p'}` summability condition into the stronger `ℒ^p` summability condition, as for sequence
-- spaces with counting measure.
/-- Exercise 4.1.1, canonical `Lp`-space form: if every measurable set has either zero measure or
measure at least some positive constant, then `L^{p'}(μ)` is a subspace of `L^p(μ)` for
`1 ≤ p' ≤ p ≤ ∞`. -/
theorem Lp_le_Lp_of_measure_lower_bound
    {p' p : ENNReal} (hp' : 1 ≤ p') (hp'le : p' ≤ p) :
    Lp ℝ p' μ ≤ Lp ℝ p μ := sorry

/-- Exercise 4.1.1 in textbook representative form: if every measurable set has either zero measure
or measure at least some positive constant, then `ℒ^{p'}(μ) ⊆ ℒ^p(μ)` for `1 ≤ p' ≤ p ≤ ∞`. -/
theorem memLp_of_memLp_of_measure_lower_bound
    {f : Ω → ℝ} {p' p : ENNReal}
    (hp' : 1 ≤ p') (hp'le : p' ≤ p) (hf : MemLp f p' μ) :
    MemLp f p μ := by
  let f' : Lp ℝ p' μ := hf.toLp f
  have hf' : ((f' : Ω →ₘ[μ] ℝ) ∈ Lp ℝ p μ) := Lp_le_Lp_of_measure_lower_bound hμ hp' hp'le f'.2
  exact MemLp.ae_eq hf.coeFn_toLp <| (Lp.mem_Lp_iff_memLp.1 hf')
