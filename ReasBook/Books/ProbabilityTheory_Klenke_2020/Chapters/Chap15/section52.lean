import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_15_52 (from Items/Chap15) -/
open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- The symmetric Pareto-type density obtained by symmetrizing the canonical Pareto density
`paretoPDFReal 1 (1 / α)` along `x ↦ |x|`. -/
def symmetricParetoDensityReal (α x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * paretoPDFReal 1 (1 / α) |x|

/-- The symmetric Pareto density is the textbook power-law density
`x ↦ (2 α)⁻¹ |x|^(-1 - 1 / α) 1_{|x| ≥ 1}(x)`. -/
theorem symmetricParetoDensityReal_eq (α x : ℝ) :
    symmetricParetoDensityReal α x =
      if 1 ≤ |x| then (1 / (2 * α)) * |x| ^ (-1 - 1 / α) else 0 := sorry

/-- The symmetric Pareto-type law on `ℝ` with Lebesgue density
`symmetricParetoDensityReal α`. -/
def symmetricParetoMeasure (α : ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (symmetricParetoDensityReal α x))

/-- The density-defined symmetric Pareto law agrees with the symmetrized canonical Pareto law
obtained by averaging `paretoMeasure 1 (1 / α)` and its reflection. -/
theorem symmetricParetoMeasure_eq_symmetrized_paretoMeasure (α : ℝ) :
    symmetricParetoMeasure α =
      (1 / 2 : ENNReal) • paretoMeasure 1 (1 / α) +
        (1 / 2 : ENNReal) • (paretoMeasure 1 (1 / α)).map (fun x ↦ -x) := sorry

-- Proof sketch: rewrite `symmetricParetoMeasure α` using
-- `symmetricParetoMeasure_eq_symmetrized_paretoMeasure`, then combine
-- `isProbabilityMeasure_paretoMeasure 1 (1 / α)` with the preserved total mass under reflection.
/-- For `α > 0`, the symmetric Pareto law has total mass `1`. -/
theorem isProbabilityMeasure_symmetricParetoMeasure (α : ℝ) (hα0 : 0 < α) :
    IsProbabilityMeasure (symmetricParetoMeasure α) := sorry

-- Proof sketch: symmetry makes the first moment vanish. For the second moment, reduce to
-- `2 * ∫_[1,∞) (2 α)⁻¹ x^(1 - 1 / α) dx`, which converges exactly when `α < 1 / 2` and evaluates
-- to `1 / (1 - 2 α)`.
/-- The symmetric Pareto law is centered and has variance `1 / (1 - 2 α)` whenever `0 < α <
1 / 2`. -/
theorem symmetricParetoMeasure_mean_variance (α : ℝ) (hα0 : 0 < α) (hα_half : α < 1 / 2) :
    (∫ x, x ∂symmetricParetoMeasure α) = 0 ∧
      Var[id; symmetricParetoMeasure α] = 1 / (1 - 2 * α) := sorry

-- Proof sketch: transport the expectation and variance identities from the pushforward law
-- `P.map X = symmetricParetoMeasure α` using `hX`, then apply
-- `symmetricParetoMeasure_mean_variance`.
/-- Example 15.52: if a real random variable has distribution with density
`x ↦ (2 α)⁻¹ |x|^(-1 - 1 / α) 1_{|x| ≥ 1}` for some `0 < α < 1 / 2`, then it has mean `0` and
variance `1 / (1 - 2 α)`. -/
theorem hasLaw_symmetricPareto_mean_variance
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (α : ℝ) (hα0 : 0 < α) (hα_half : α < 1 / 2)
    (hX : HasLaw X (symmetricParetoMeasure α) P) :
    P[X] = 0 ∧ Var[X; P] = 1 / (1 - 2 * α) := sorry

end
