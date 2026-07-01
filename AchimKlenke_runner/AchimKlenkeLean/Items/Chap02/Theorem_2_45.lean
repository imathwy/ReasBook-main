import AchimKlenkeLean.Items.Chap02.Definition_2_44

open scoped unitInterval
open unitInterval

-- Declarations for this item will be appended below by the statement pipeline.

/-- In dimension `1`, the critical percolation value is `1`. -/
theorem criticalPercolationProbability_eq_one
    (θ : ℕ → unitInterval → NNReal)
    (h_dim_one_subcritical :
      ∀ p : unitInterval, (p : ℝ) < 1 → θ 1 p = 0)
    (h_dim_one_open : 0 < θ 1 (1 : unitInterval)) :
    criticalPercolationValue (θ 1) = 1 := sorry

-- Proof sketch: use the one-dimensional subcritical vanishing assumption to show that no
-- parameter below `1` belongs to the positive-probability set, use positivity at `p = 1` to show
-- that `1` does belong to that set, and then combine the lower bound
-- `(1 : ℝ) / (2 * d - 1) ≤ criticalPercolationValue (θ d)` from the subcritical estimate with the
-- upper bound `(criticalPercolationValue (θ d) : ℝ) ≤ 2 / 3` obtained from the two-dimensional
-- supercritical estimate and antitonicity in the dimension.
/-- For dimensions `d ≥ 2`, the underlying real number of the critical percolation value lies in
`[(2d - 1)⁻¹, 2 / 3]`. -/
theorem criticalPercolationProbability_mem_Icc
    (θ : ℕ → unitInterval → NNReal)
    (h_subcritical :
      ∀ ⦃d : ℕ⦄, 2 ≤ d →
        ∀ p : unitInterval, (p : ℝ) < (1 : ℝ) / (2 * d - 1) → θ d p = 0)
    (h_two_dim_supercritical :
      ∀ p : unitInterval, (2 : ℝ) / 3 < (p : ℝ) → 0 < θ 2 p)
    (h_antitone : Antitone (fun d ↦ criticalPercolationValue (θ d)))
    {d : ℕ} (hd : 2 ≤ d) :
    (criticalPercolationValue (θ d) : ℝ) ∈
      Set.Icc ((1 : ℝ) / (2 * d - 1)) ((2 : ℝ) / 3) := sorry

/-- Theorem 2.45: the critical percolation probability equals `1` in dimension `1`, and for
dimensions `d ≥ 2` its underlying real value lies in the interval `[(2d - 1)⁻¹, 2/3]`. -/
theorem criticalPercolationProbability_eq_one_and_mem_Icc
    (θ : ℕ → unitInterval → NNReal)
    (h_dim_one_subcritical :
      ∀ p : unitInterval, (p : ℝ) < 1 → θ 1 p = 0)
    (h_dim_one_open : 0 < θ 1 (1 : unitInterval))
    (h_subcritical :
      ∀ ⦃d : ℕ⦄, 2 ≤ d →
        ∀ p : unitInterval, (p : ℝ) < (1 : ℝ) / (2 * d - 1) → θ d p = 0)
    (h_two_dim_supercritical :
      ∀ p : unitInterval, (2 : ℝ) / 3 < (p : ℝ) → 0 < θ 2 p)
    (h_antitone : Antitone (fun d ↦ criticalPercolationValue (θ d)))
    :
    criticalPercolationValue (θ 1) = 1 ∧
      ∀ ⦃d : ℕ⦄, 2 ≤ d →
        (criticalPercolationValue (θ d) : ℝ) ∈
          Set.Icc ((1 : ℝ) / (2 * d - 1)) ((2 : ℝ) / 3) := by
  constructor
  · exact criticalPercolationProbability_eq_one θ h_dim_one_subcritical h_dim_one_open
  · intro d hd
    exact criticalPercolationProbability_mem_Icc θ h_subcritical h_two_dim_supercritical
      h_antitone hd
