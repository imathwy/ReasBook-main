import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_47 (from Items/Chap21) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The textbook Laplace transform of the branching diffusion started from `x` and observed at time
`t`. -/
def branchingDiffusionLaplaceTransform (t x : NNReal) : ℝ → ℝ :=
  fun l ↦ Real.exp (-((x : ℝ) * l / (l * (t : ℝ) + 1)))

/-- Evaluating `branchingDiffusionLaplaceTransform` gives the explicit exponential formula
`exp (-x λ / (1 + t λ))`. -/
theorem branchingDiffusionLaplaceTransform_apply (t x : NNReal) (l : ℝ) :
    branchingDiffusionLaplaceTransform t x l =
      Real.exp (-((x : ℝ) * l / (l * (t : ℝ) + 1))) :=
  rfl

section BranchingDiffusion

variable {κ : NNReal → Kernel NNReal NNReal}
variable {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
variable (hY : IsMarkovProcessRealization κ P Y)
variable (hκ : HasBranchingDiffusionLaplaceTransform κ)

/-- A realization of a branching-diffusion kernel inherits the textbook one-time Laplace-transform
formula, with the source-faithful Laplace parameter domain `λ ≥ 0`. -/
theorem IsMarkovProcessRealization.branchingDiffusionLaplaceTransform
    (x t l : NNReal) :
    ∫ ω, Real.exp (-((l : ℝ) * (Y t ω : ℝ))) ∂(P x : Measure Ω) =
      branchingDiffusionLaplaceTransform t x l := sorry

-- Proof sketch: use the Markov-process realization from Lemma 21.46, identify the linear test
-- function `y ↦ (y : ℝ)` as harmonic for the branching-diffusion semigroup by the first-moment
-- computation from the Laplace formula, and apply the Markov-process martingale criterion with
-- respect to the natural filtration of `Y`.
/-- Lemma 21.47: for a realization of the branching-diffusion semigroup from Lemma 21.46, the
coordinate process `Y` is a martingale with respect to its natural filtration under each initial
law `P x`. -/
theorem branchingDiffusion_martingale (x : NNReal) :
    Martingale (fun t ω ↦ (Y t ω : ℝ))
      (Filtration.natural Y
        (fun t ↦ ((hY.hasNaturalMarkovProperty x).1 t).stronglyMeasurable))
      (P x : Measure Ω) := sorry

-- Proof sketch: identify the Laplace transform of `Y t` with
-- `branchingDiffusionLaplaceTransform t x`, differentiate the identity `k` times at `λ = 0`,
-- and use the standard relation between derivatives of `λ ↦ E_x[exp (-λ Y_t)]` and moments.
/-- Lemma 21.47: for a realization of the branching-diffusion semigroup, the `k`th marginal moment
at time `t` is obtained by differentiating the textbook Laplace transform at `0`. -/
theorem branchingDiffusion_moment_eq_neg_one_pow_iteratedDeriv
    {x t : NNReal} (k : ℕ) :
    moment (fun ω ↦ (Y t ω : ℝ)) k (P x : Measure Ω) =
      (-1 : ℝ) ^ k * iteratedDeriv k (branchingDiffusionLaplaceTransform t x) 0 := sorry

-- Proof sketch: specialize
-- `branchingDiffusion_moment_eq_neg_one_pow_iteratedDeriv` to `k = 1` and evaluate the first
-- derivative of `λ ↦ exp (-x λ / (1 + t λ))` at `0`.
/-- The first moment of the branching diffusion remains equal to the initial state `x`. -/
theorem branchingDiffusion_first_moment
    {x t : NNReal} :
    moment (fun ω ↦ (Y t ω : ℝ)) 1 (P x : Measure Ω) = x := sorry

-- Proof sketch: differentiate the Laplace transform twice at `0`, or specialize the general
-- moment formula with `k = 2` and simplify the resulting polynomial.
/-- The second moment of the branching diffusion is `2xt + x²`. -/
theorem branchingDiffusion_second_moment
    {x t : NNReal} :
    moment (fun ω ↦ (Y t ω : ℝ)) 2 (P x : Measure Ω) =
      2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := sorry

-- Proof sketch: differentiate the Laplace transform three times at `0` and simplify the
-- coefficient expansion.
/-- The third moment of the branching diffusion is `6xt² + 6x²t + x³`. -/
theorem branchingDiffusion_third_moment
    {x t : NNReal} :
    moment (fun ω ↦ (Y t ω : ℝ)) 3 (P x : Measure Ω) =
      6 * (x : ℝ) * (t : ℝ) ^ 2 + 6 * (x : ℝ) ^ 2 * (t : ℝ) + (x : ℝ) ^ 3 := sorry

-- Proof sketch: differentiate the Laplace transform four times at `0` and collect the resulting
-- polynomial coefficients.
/-- The fourth moment of the branching diffusion is `24xt³ + 36x²t² + 12x³t + x⁴`. -/
theorem branchingDiffusion_fourth_moment
    {x t : NNReal} :
    moment (fun ω ↦ (Y t ω : ℝ)) 4 (P x : Measure Ω) =
      24 * (x : ℝ) * (t : ℝ) ^ 3 + 36 * (x : ℝ) ^ 2 * (t : ℝ) ^ 2 +
        12 * (x : ℝ) ^ 3 * (t : ℝ) + (x : ℝ) ^ 4 := sorry

-- Proof sketch: differentiate the Laplace transform five times at `0` and simplify the resulting
-- coefficients.
/-- The fifth moment of the branching diffusion is `120xt⁴ + 240x²t³ + 120x³t² + 20x⁴t + x⁵`. -/
theorem branchingDiffusion_fifth_moment
    {x t : NNReal} :
    moment (fun ω ↦ (Y t ω : ℝ)) 5 (P x : Measure Ω) =
      120 * (x : ℝ) * (t : ℝ) ^ 4 + 240 * (x : ℝ) ^ 2 * (t : ℝ) ^ 3 +
        120 * (x : ℝ) ^ 3 * (t : ℝ) ^ 2 + 20 * (x : ℝ) ^ 4 * (t : ℝ) +
        (x : ℝ) ^ 5 := sorry

-- Proof sketch: differentiate the Laplace transform six times at `0` and collect the polynomial
-- coefficients of the resulting expression.
/-- The sixth moment of the branching diffusion is
`720xt⁵ + 1800x²t⁴ + 1200x³t³ + 300x⁴t² + 30x⁵t + x⁶`. -/
theorem branchingDiffusion_sixth_moment
    {x t : NNReal} :
    moment (fun ω ↦ (Y t ω : ℝ)) 6 (P x : Measure Ω) =
      720 * (x : ℝ) * (t : ℝ) ^ 5 + 1800 * (x : ℝ) ^ 2 * (t : ℝ) ^ 4 +
        1200 * (x : ℝ) ^ 3 * (t : ℝ) ^ 3 + 300 * (x : ℝ) ^ 4 * (t : ℝ) ^ 2 +
        30 * (x : ℝ) ^ 5 * (t : ℝ) + (x : ℝ) ^ 6 := sorry

-- Proof sketch: use the first-moment identity to rewrite the second central moment around the
-- mean `x`, expand `centralMoment`, and simplify with the explicit raw second moment formula.
/-- The second centered moment of the branching diffusion is `2xt`. -/
theorem branchingDiffusion_second_centralMoment
    {x t : NNReal} :
    centralMoment (fun ω ↦ (Y t ω : ℝ)) 2 (P x : Measure Ω) =
      2 * (x : ℝ) * (t : ℝ) := sorry

-- Proof sketch: expand the third centered moment in terms of the raw moments, then substitute the
-- first and third moment formulas and simplify.
/-- The third centered moment of the branching diffusion is `6xt²`. -/
theorem branchingDiffusion_third_centralMoment
    {x t : NNReal} :
    centralMoment (fun ω ↦ (Y t ω : ℝ)) 3 (P x : Measure Ω) =
      6 * (x : ℝ) * (t : ℝ) ^ 2 := sorry

-- Proof sketch: expand the fourth centered moment via the binomial formula, substitute the raw
-- moment identities, and collect coefficients.
/-- The fourth centered moment of the branching diffusion is `24xt³ + 12x²t²`. -/
theorem branchingDiffusion_fourth_centralMoment
    {x t : NNReal} :
    centralMoment (fun ω ↦ (Y t ω : ℝ)) 4 (P x : Measure Ω) =
      24 * (x : ℝ) * (t : ℝ) ^ 3 + 12 * (x : ℝ) ^ 2 * (t : ℝ) ^ 2 := sorry

-- Proof sketch: express the fifth centered moment in terms of raw moments, then substitute the
-- formulas up to order five and simplify.
/-- The fifth centered moment of the branching diffusion is `120xt⁴ + 120x²t³`. -/
theorem branchingDiffusion_fifth_centralMoment
    {x t : NNReal} :
    centralMoment (fun ω ↦ (Y t ω : ℝ)) 5 (P x : Measure Ω) =
      120 * (x : ℝ) * (t : ℝ) ^ 4 + 120 * (x : ℝ) ^ 2 * (t : ℝ) ^ 3 := sorry

-- Proof sketch: expand the sixth centered moment, substitute the raw moments through order six,
-- and collect the remaining polynomial terms.
/-- The sixth centered moment of the branching diffusion is
`720xt⁵ + 1080x²t⁴ + 120x³t³`. -/
theorem branchingDiffusion_sixth_centralMoment
    {x t : NNReal} :
    centralMoment (fun ω ↦ (Y t ω : ℝ)) 6 (P x : Measure Ω) =
      720 * (x : ℝ) * (t : ℝ) ^ 5 + 1080 * (x : ℝ) ^ 2 * (t : ℝ) ^ 4 +
        120 * (x : ℝ) ^ 3 * (t : ℝ) ^ 3 := sorry

end BranchingDiffusion

end ProbabilityTheory
