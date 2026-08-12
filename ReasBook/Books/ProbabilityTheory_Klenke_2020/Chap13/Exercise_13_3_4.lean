import ProbabilityTheory_Klenke_2020.Chap13.Theorem_13_29

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open MeasureTheory.FiniteMeasure
open scoped Topology

/-- A real-valued function on `ℝ^d`, modeled as `(Fin d → ℝ) → ℝ`, belongs to the multivariate
Helly class `V_d` when it is coordinatewise monotone, right continuous from the upper orthant
`Set.Ici x` at every `x`, and bounded. -/
class IsCoordinatewiseRightContinuousMonotoneBoundedFunction {d : ℕ}
    (F : (Fin d → ℝ) → ℝ) : Prop where
  right_continuous : ∀ x : Fin d → ℝ, ContinuousWithinAt F (Set.Ici x) x
  monotone : Monotone F
  bounded : ∃ C : ℝ, ∀ x : Fin d → ℝ, ‖F x‖ ≤ C

/-- Constant functions on `ℝ^d` belong to the multivariate Helly class `V_d`. -/
instance instIsCoordinatewiseRightContinuousMonotoneBoundedFunctionConst {d : ℕ} (c : ℝ) :
    IsCoordinatewiseRightContinuousMonotoneBoundedFunction (fun _ : Fin d → ℝ ↦ c) := sorry

/-- A subsequence `u ∘ φ` converges to `F` in the multivariate Helly sense if `φ` is strictly
increasing, the limit function `F` again belongs to `V_d`, and the subsequence converges pointwise
at every continuity point of `F`. -/
class IsHellySubsequenceLimitInRd {d : ℕ}
    (u : ℕ → (Fin d → ℝ) → ℝ) (φ : ℕ → ℕ) (F : (Fin d → ℝ) → ℝ) : Prop where
  strictMono : StrictMono φ
  limit_mem : IsCoordinatewiseRightContinuousMonotoneBoundedFunction F
  tendsto_at_continuity_points :
    ∀ ⦃x : Fin d → ℝ⦄, ContinuousAt F x →
      Tendsto (fun k ↦ u (φ k) x) atTop (𝓝 (F x))

-- Proof sketch: use the multidimensional Helly diagonal extraction on a countable dense subset of
-- `ℝ^d`, define the limit by the upper-orthant envelope of the pointwise subsequential limits, and
-- then use coordinatewise monotonicity together with right continuity to upgrade convergence to
-- every continuity point of the limit function.
/-- Exercise 13.3.4 (1): Item (i). Helly's theorem remains valid for the multivariate class `V_d`
of coordinatewise monotone, bounded, right-continuous functions on `ℝ^d`. -/
theorem exists_helly_subsequence_tendsto_at_continuity_points_in_Rd
    (d : ℕ) (u : ℕ → (Fin d → ℝ) → ℝ)
    (hV : ∀ n : ℕ, IsCoordinatewiseRightContinuousMonotoneBoundedFunction (u n))
    (h_uniform : ∃ C : ℝ, ∀ n (x : Fin d → ℝ), ‖u n x‖ ≤ C) :
    ∃ φ : ℕ → ℕ, ∃ F : (Fin d → ℝ) → ℝ, IsHellySubsequenceLimitInRd u φ F := sorry

-- Proof sketch: identify each subprobability finite measure on `ℝ^d` with its lower-orthant
-- distribution function, apply the multidimensional Helly theorem from part (1) to obtain
-- subsequential weak limits, and use the standard Polish-space converse on `ℝ^d` to recover
-- tightness from weak relative sequential compactness.
/-- Exercise 13.3.4 (2): Item (ii). Prohorov's theorem holds on `ℝ^d`, modeled as `Fin d → ℝ`, so
for subprobability finite measures tightness is equivalent to weak relative sequential
compactness. -/
theorem prohorov_theorem_iff_tight_in_Rd
    (d : ℕ) (ℱ : Set (FiniteMeasure (Fin d → ℝ)))
    (hℱ : ∀ μ ∈ ℱ, μ.mass ≤ 1) :
    IsTightMeasureSet (((↑) : FiniteMeasure (Fin d → ℝ) → Measure (Fin d → ℝ)) '' ℱ) ↔
      (∀ μs : ℕ → FiniteMeasure (Fin d → ℝ), (∀ n, μs n ∈ ℱ) →
        ∃ μ : FiniteMeasure (Fin d → ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
          Tendsto (μs ∘ φ) atTop (𝓝 μ)) := by
  constructor
  · exact isWeaklyRelativelySequentiallyCompactFamily_of_isTightMeasureSet ℱ hℱ
  · exact isTightMeasureSet_of_isWeaklyRelativelySequentiallyCompactFamily ℱ hℱ
