import ProbabilityTheory_Klenke_2020.Chap15.Example_15_16

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

attribute [local instance] Classical.propDecidable

/- Reuse the odd-square atomic law from Example 15.16 via its owner `PMF` presentation. -/
local notation "μodd" => oddSquarePMF.toMeasure.map fun x : ℤ ↦ x

/-- The measure `ν = 1/2 δ_0 + 1/2 (x ↦ 2x)_* μ`, equivalently
`ν (A) = 1/2 * δ_0(A) + 1/2 * μ (A / 2)`, that appears in the tent-function characteristic
function example. -/
noncomputable def halfDiracPlusDoubleMapMeasure (μ : Measure ℝ) : Measure ℝ :=
  (1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • μ.map (fun x ↦ (2 : ℝ) * x)

/-- The predicate that a real number is an odd integer. -/
def IsOddIntegerReal (x : ℝ) : Prop :=
  ∃ k : ℤ, Odd k ∧ x = k

-- Proof sketch: expand `halfDiracPlusDoubleMapMeasure`, use linearity of the integral defining
-- `MeasureTheory.charFun`, rewrite the Dirac term with `MeasureTheory.charFun_dirac`, and rewrite
-- the pushforward term with `MeasureTheory.charFun_map_mul`.
/-- The characteristic function of `halfDiracPlusDoubleMapMeasure μ` is
`t ↦ 1 / 2 + (1 / 2) * φ_μ(2 t)`. -/
theorem charFun_halfDiracPlusDoubleMapMeasure_eq (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    charFun (halfDiracPlusDoubleMapMeasure μ) t =
      (1 / 2 : ℂ) + (1 / 2 : ℂ) * charFun μ ((2 : ℝ) * t) := sorry

-- Proof sketch: evaluate `halfDiracPlusDoubleMapMeasure μodd` on the singleton `{x}`, use
-- `Measure.map_apply` for the doubling map and the odd-square singleton formula coming from
-- `μodd`, then split into the cases `x = 0`,
-- `x / 2` odd, and the remaining case.
/-- Example 15.17: for `μ = μodd`, the measure
`ν = 1/2 δ_0 + 1/2 (x ↦ 2x)_* μ` satisfies `ν({0}) = 1/2`, `ν({x}) = 8 / (π^2 x^2)` when
`x / 2` is an odd integer, and `ν({x}) = 0` otherwise. -/
theorem halfDiracPlusDoubleMapMeasure_real_singleton_eq (x : ℝ) :
    (halfDiracPlusDoubleMapMeasure μodd).real ({x} : Set ℝ) =
      if x = 0 then
        1 / 2
      else if IsOddIntegerReal (x / 2) then
        8 / (Real.pi ^ 2 * x ^ 2)
      else
        0 := sorry
