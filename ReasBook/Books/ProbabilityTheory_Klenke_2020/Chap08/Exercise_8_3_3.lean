import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

def closedUnitDisc : Set (ℝ × ℝ) :=
  {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}

def unitSquare : Set (ℝ × ℝ) :=
  Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1

/-- The uniform law on the closed unit disc in `ℝ²`. -/
def unitDiscUniformMeasure : Measure (ℝ × ℝ) :=
  volume[|closedUnitDisc]

/-- The uniform law on the square `[-1,1]^2` in `ℝ²`. -/
def unitSquareUniformMeasure : Measure (ℝ × ℝ) :=
  volume[|unitSquare]

private theorem closedUnitDisc_subset_unitSquare : closedUnitDisc ⊆ unitSquare := by
  intro z hz
  change z.1 ^ 2 + z.2 ^ 2 ≤ 1 at hz
  rw [unitSquare]
  constructor
  · constructor
    · nlinarith [sq_nonneg z.2, hz]
    · nlinarith [sq_nonneg z.2, hz]
  · constructor
    · nlinarith [sq_nonneg z.1, hz]
    · nlinarith [sq_nonneg z.1, hz]

private theorem halfUnitSquare_subset_closedUnitDisc :
    (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) : Set (ℝ × ℝ)) ⊆
      closedUnitDisc := by
  intro z hz
  rcases hz with ⟨hx, hy⟩
  have hx_sq : z.1 ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [hx.1, hx.2]
  have hy_sq : z.2 ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [hy.1, hy.2]
  change z.1 ^ 2 + z.2 ^ 2 ≤ 1
  nlinarith

private theorem volume_unitSquare_pos : 0 < volume unitSquare := by
  rw [unitSquare, Measure.volume_eq_prod, Measure.prod_prod]
  norm_num [Real.volume_Icc]

private theorem volume_unitSquare_ne_top : volume unitSquare ≠ ⊤ := by
  rw [unitSquare, Measure.volume_eq_prod, Measure.prod_prod]
  norm_num [Real.volume_Icc]

private theorem volume_closedUnitDisc_pos : 0 < volume closedUnitDisc := by
  refine lt_of_lt_of_le ?_ (measure_mono halfUnitSquare_subset_closedUnitDisc)
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  norm_num [Real.volume_Icc]

private theorem volume_closedUnitDisc_ne_top : volume closedUnitDisc ≠ ⊤ := by
  refine ne_of_lt <| lt_of_le_of_lt (measure_mono closedUnitDisc_subset_unitSquare) ?_
  exact lt_top_iff_ne_top.mpr volume_unitSquare_ne_top

-- Proof sketch: apply the standard fact that conditioned Lebesgue measure on a set of positive
-- finite volume is a probability measure; here the unit disc has finite positive area.
/-- The uniform law on the closed unit disc is a probability measure. -/
instance : IsProbabilityMeasure unitDiscUniformMeasure := by
  rw [unitDiscUniformMeasure]
  exact cond_isProbabilityMeasure_of_finite volume_closedUnitDisc_pos.ne' volume_closedUnitDisc_ne_top

-- Proof sketch: apply the same conditioned-volume probability-measure fact to the square
-- `[-1,1]^2`, whose Lebesgue measure is finite and nonzero.
/-- The uniform law on `[-1,1]^2` is a probability measure. -/
instance : IsProbabilityMeasure unitSquareUniformMeasure := by
  rw [unitSquareUniformMeasure]
  exact cond_isProbabilityMeasure_of_finite volume_unitSquare_pos.ne' volume_unitSquare_ne_top

/-- The radius `R = sqrt (x^2 + y^2)` associated to a point `(x, y) ∈ ℝ²`. -/
abbrev planarRadius (z : ℝ × ℝ) : ℝ :=
  Real.sqrt (z.1 ^ 2 + z.2 ^ 2)

/-- The textbook angle variable `Θ = arctan (y / x)`. In Lean, division by `0` is defined, so
this gives a total measurable function on `ℝ²`. -/
abbrev principalAngle (z : ℝ × ℝ) : ℝ :=
  Real.arctan (z.2 / z.1)

/-- The support of the principal angle on the circle of radius `r` inside the square `[-1,1]^2`.
-/
def squarePrincipalAngleSupport (r : ℝ) : Set ℝ :=
  Set.Icc (-(Real.pi / 2)) (Real.pi / 2) ∩
    {θ | 0 ≤ r ∧ r * |Real.cos θ| ≤ 1 ∧ r * |Real.sin θ| ≤ 1}

-- Proof sketch: view the unit-disc law as a constant density on the disc and apply the density
-- formula for regular conditional distributions. The marginal in `x` is proportional to the length
-- of the vertical chord, so the fiber law is the normalized Lebesgue measure on that chord.
/-- Exercise 8.3.3 (1): In part (i), for the uniform law on the unit disc, the conditional
distribution of `Y` given `X = x` is the uniform law on
`[-sqrt (1 - x^2), sqrt (1 - x^2)]` for `P.map X`-almost every `x`. -/
theorem condDistrib_snd_given_fst_unitDisc_ae_eq_uniform_segment :
    ∀ᵐ x ∂(unitDiscUniformMeasure.map Prod.fst),
      condDistrib Prod.snd Prod.fst unitDiscUniformMeasure x =
        volume[|Set.Icc (-Real.sqrt (1 - x ^ 2)) (Real.sqrt (1 - x ^ 2))] := sorry

-- Proof sketch: identify the uniform law on `[-1,1]^2` with the product of the two uniform laws
-- on `[-1,1]` and use the a.e.-uniqueness of `condDistrib` for a product decomposition.
/-- Exercise 8.3.3 (2): In part (i), for the uniform law on `[-1,1]^2`, the conditional
distribution of `Y` given `X = x` is the uniform law on `[-1,1]` for `P.map X`-almost every
`x`. -/
theorem condDistrib_snd_given_fst_unitSquare_ae_eq_uniform_interval :
    ∀ᵐ x ∂(unitSquareUniformMeasure.map Prod.fst),
      condDistrib Prod.snd Prod.fst unitSquareUniformMeasure x =
        volume[|Set.Icc (-1 : ℝ) 1] := sorry

-- Proof sketch: pass to polar coordinates on the disc. The angular component is independent of
-- the radius and is uniform on the full circle; pushing that law forward by the principal-angle
-- map gives the uniform law on `[-π / 2, π / 2]`.
/-- Exercise 8.3.3 (3): In part (ii), for the uniform law on the unit disc, the conditional
distribution of `Θ = arctan (Y / X)` given `R = sqrt (X^2 + Y^2)` is the uniform law on
`[-π / 2, π / 2]` for `P.map R`-almost every `r`. -/
theorem condDistrib_principalAngle_given_radius_unitDisc_ae_eq_uniform_interval :
    ∀ᵐ r ∂(unitDiscUniformMeasure.map planarRadius),
      condDistrib principalAngle planarRadius unitDiscUniformMeasure r =
        volume[|Set.Icc (-(Real.pi / 2)) (Real.pi / 2)] := sorry

-- Proof sketch: condition on the radius and describe the fiber as the arc of the circle of radius
-- `r` lying in `[-1,1]^2`. The conditional law is uniform in arc length on that fiber, and the
-- principal-angle map pushes it forward to the conditioned Lebesgue measure on the angle support.
/-- Exercise 8.3.3 (4): In part (ii), for the uniform law on `[-1,1]^2`, the conditional
distribution of `Θ = arctan (Y / X)` given `R = sqrt (X^2 + Y^2)` is the uniform law on the
principal-angle support cut out by the circle of radius `r` inside the square, for `P.map R`-almost
every `r`. -/
theorem condDistrib_principalAngle_given_radius_unitSquare_ae_eq_uniform_support :
    ∀ᵐ r ∂(unitSquareUniformMeasure.map planarRadius),
      condDistrib principalAngle planarRadius unitSquareUniformMeasure r =
        volume[|squarePrincipalAngleSupport r] := sorry
