import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u v

variable {ι : Type u} [Fintype ι] {E : ι → Type v}
variable [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, NormedSpace ℝ (E i)]

/-- Definition 1.37: the composite weighted `l_2` formula on the finite product
`∏ i, E i`, modeling a finite block product, is the
canonical `PiLp` `L²` norm of the componentwise rescaled family. Written out in coordinates, this
is the textbook weighted `l_2` norm with strictly positive weights. -/
def compositeWeightedL2Norm (ω : ι → Set.Ioi (0 : ℝ)) (u : ∀ i, E i) : ℝ :=
  ‖WithLp.toLp (2 : ENNReal) (fun i ↦ Real.sqrt (ω i : ℝ) • u i)‖

-- Proof sketch: apply `PiLp.norm_eq_of_L2` to the rescaled family
-- `fun i ↦ √ωᵢ • uᵢ`, then simplify `‖√ωᵢ • uᵢ‖² = ωᵢ ‖uᵢ‖²` using positivity of `ω i`.
/-- The composite weighted `l_2` norm is the textbook square-root-of-weighted-sum formula. -/
theorem compositeWeightedL2Norm_def (ω : ι → Set.Ioi (0 : ℝ)) (u : ∀ i, E i) :
    compositeWeightedL2Norm ω u = √(∑ i, (ω i : ℝ) * ‖u i‖ ^ (2 : ℕ)) := by
  rw [compositeWeightedL2Norm, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (ω i).2.le]

-- Proof sketch: square the defining formula, use the positivity hypothesis on `ω` together with
-- nonnegativity of `‖u i‖ ^ 2`, and conclude from vanishing of the weighted sum that every
-- component norm is zero.
/-- With strictly positive weights, the composite weighted `l_2`-norm vanishes exactly on the zero
family. -/
theorem compositeWeightedL2Norm_eq_zero_iff (ω : ι → Set.Ioi (0 : ℝ)) (u : ∀ i, E i) :
    compositeWeightedL2Norm ω u = 0 ↔ u = 0 := sorry

end
