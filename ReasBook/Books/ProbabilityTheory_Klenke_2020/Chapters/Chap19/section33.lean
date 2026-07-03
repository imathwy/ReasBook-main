import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_19_33 (from Items/Chap19) -/
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/- Layering for Theorem 19.33:
- `source-facing`: the one-dimensional random environment `W` on `ℤ`, its local ratios
  `ρ(x) = (1 - W.rightJumpProb x) / W.rightJumpProb x`, the textbook series `R_w^-`, `R_w^+`, and
  the drift-to-`±∞` / oscillation conclusions.
- `core/canonical`: the Chapter 19 conductance owner `effectiveResistanceToInfinity`.
- `bridge/view`: a reversible nearest-neighbor conductance family derived from the ratio products,
  used only to connect the RWRE series to the Chapter 19 electrical-network API. -/

/-- The local Solomon ratio `ρ(x) = q(x) / p(x)` of the environment `W`, where
`p(x) = W.rightJumpProb x` and `q(x) = 1 - p(x)`. -/
def randomEnvironmentRatio (W : RandomEnvironment) (x : ℤ) : ℝ≥0∞ :=
  ((1 : ℝ≥0∞) - W.rightJumpProb x) / W.rightJumpProb x

scoped[ProbabilityTheory] notation "ρ[" W "](" x ")" => randomEnvironmentRatio W x

/-- The `n`-th rightward multiplicative term in Solomon's series `R_w^+`, namely
`∏_{k=0}^n ρ(k)`. -/
def randomEnvironmentRightSeriesTerm (W : RandomEnvironment) (n : ℕ) : ℝ≥0∞ :=
  Finset.prod (Finset.range (n + 1)) fun k ↦ ρ[W](k)

/-- The `n`-th leftward multiplicative term in Solomon's series `R_w^-`, namely
`∏_{k=-n}^{-1} ρ(k)⁻¹`, with the convention that the empty product for `n = 0` is `1`. -/
def randomEnvironmentLeftSeriesTerm (W : RandomEnvironment) (n : ℕ) : ℝ≥0∞ :=
  Finset.prod (Finset.range n) fun k ↦ (ρ[W](-((k : ℤ) + 1)))⁻¹

/-- The textbook right-hand Solomon series `R_w^+ = ∑_{n ≥ 0} ∏_{k=0}^n ρ(k)`. -/
def randomEnvironmentRightSeries (W : RandomEnvironment) : ℝ≥0∞ :=
  ∑' n : ℕ, randomEnvironmentRightSeriesTerm W n

scoped[ProbabilityTheory] notation "R⁺[" W "]" => randomEnvironmentRightSeries W

/-- The textbook left-hand Solomon series
`R_w^- = ∑_{n ≥ 0} ∏_{k=-n}^{-1} ρ(k)⁻¹`, where the `n = 0` term is the empty product `1`. -/
def randomEnvironmentLeftSeries (W : RandomEnvironment) : ℝ≥0∞ :=
  ∑' n : ℕ, randomEnvironmentLeftSeriesTerm W n

scoped[ProbabilityTheory] notation "R⁻[" W "]" => randomEnvironmentLeftSeries W

/-- Expanding `R_w^+` gives the textbook series `∑_{n ≥ 0} ∏_{k=0}^n ρ(k)`. -/
@[simp]
theorem randomEnvironmentRightSeries_def (W : RandomEnvironment) :
    R⁺[W] = ∑' n : ℕ, randomEnvironmentRightSeriesTerm W n := rfl

/-- Expanding `R_w^-` gives the textbook series
`∑_{n ≥ 0} ∏_{k=-n}^{-1} ρ(k)⁻¹`, with empty `n = 0` term equal to `1`. -/
@[simp]
theorem randomEnvironmentLeftSeries_def (W : RandomEnvironment) :
    R⁻[W] = ∑' n : ℕ, randomEnvironmentLeftSeriesTerm W n := rfl

/-- Solomon's directional series ratio `toward / (away + toward)`, interpreted with the textbook
convention `∞ / ∞ = 1` in the asymmetric transience regime where `toward = ∞` and `away < ∞`. -/
def solomonDirectionalSeriesRatio (toward away : ℝ≥0∞) : ℝ≥0∞ :=
  if toward = ∞ then 1 else toward / (away + toward)

/-- When the series in the chosen direction is finite, Solomon's directional ratio is the usual
`ℝ≥0∞` quotient. -/
theorem solomonDirectionalSeriesRatio_eq_div {toward away : ℝ≥0∞} (htoward : toward < ∞) :
    solomonDirectionalSeriesRatio toward away = toward / (away + toward) := by
  simp [solomonDirectionalSeriesRatio, htoward.ne]

/-- When the series in the chosen direction is infinite, Solomon's source convention makes the
directional ratio equal to `1`. -/
@[simp]
theorem solomonDirectionalSeriesRatio_eq_one {toward away : ℝ≥0∞} (htoward : toward = ∞) :
    solomonDirectionalSeriesRatio toward away = 1 := by
  simp [solomonDirectionalSeriesRatio, htoward]

/-- The reversible edge conductance attached to the edge `{x, x + 1}` of the environment `W`.
For `x ≥ 0` it is the reciprocal of the prefix product `∏_{k=0}^x ρ(k)`, while for `x < 0` it is
the reciprocal of `∏_{k=x+1}^{-1} ρ(k)⁻¹`. This is a bridge object, not the main RWRE owner. -/
def randomEnvironmentEdgeConductance (W : RandomEnvironment) (x : ℤ) : ℝ≥0∞ :=
  if 0 ≤ x then
    (randomEnvironmentRightSeriesTerm W x.toNat)⁻¹
  else
    (randomEnvironmentLeftSeriesTerm W (Int.natAbs (x + 1)))⁻¹

/-- The nearest-neighbor conductance family on `ℤ` derived from the environment `W`: the edge
`{x, x + 1}` carries the conductance `randomEnvironmentEdgeConductance W x`. This is the
conductance-network bridge used to access the Chapter 19 owner API. -/
def randomEnvironmentConductance (W : RandomEnvironment) : ℤ → ℤ → ℝ≥0∞ :=
  fun x y ↦
    if y = x + 1 then
      randomEnvironmentEdgeConductance W x
    else if y = x - 1 then
      randomEnvironmentEdgeConductance W (x - 1)
    else
      0

/-- Evaluating the environment-derived conductance family gives the two adjacent edge weights. -/
@[simp]
theorem randomEnvironmentConductance_apply (W : RandomEnvironment) (x y : ℤ) :
    randomEnvironmentConductance W x y =
      if y = x + 1 then
        randomEnvironmentEdgeConductance W x
      else if y = x - 1 then
        randomEnvironmentEdgeConductance W (x - 1)
      else
        0 := rfl

section Bridge

variable {W : RandomEnvironment}

-- Proof sketch: the ratio recursion defining `randomEnvironmentEdgeConductance` gives
-- `randomEnvironmentEdgeConductance W (x - 1) /
--   randomEnvironmentEdgeConductance W x = ρ[W](x)`. Rewriting this as
-- `q(x) / p(x)` shows that row-normalizing the bridge conductances reproduces the source-facing
-- owner matrix `randomEnvironmentTransitionMatrix W`.
/-- For an environment with positive left- and right-jump probabilities, the Chapter 19
conductance walk associated to `randomEnvironmentConductance W` has transition matrix equal to the
source-facing RWRE owner `randomEnvironmentTransitionMatrix W`. -/
theorem randomEnvironmentTransitionMatrix_eq_conductanceTransitionMatrix
    (hW : W.IsElliptic)
    (x y : ℤ) :
    randomEnvironmentTransitionMatrix W x y =
      conductanceTransitionMatrix (randomEnvironmentConductance W) x y := sorry

/-- Under the canonical RWRE realization owner from Definition 19.34, ellipticity lets one
transport the realization to the Chapter 19 conductance-walk bridge. -/
theorem isMarkovProcessRealization_randomEnvironmentConductance
    {P : ℤ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℤ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    (hW : W.IsElliptic) :
    IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel (conductanceTransitionMatrix (randomEnvironmentConductance W)) ^ n)
      P X := by
  have htransition :
      randomEnvironmentTransitionMatrix W =
        conductanceTransitionMatrix (randomEnvironmentConductance W) := by
    funext x y
    exact randomEnvironmentTransitionMatrix_eq_conductanceTransitionMatrix hW x y
  simpa [htransition] using
    (inferInstance :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X)

end Bridge

section RWRERealization

variable (W : RandomEnvironment) (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]

-- Proof sketch: the two rays `(-∞, 0]` and `[0, ∞)` form parallel branches of the bridge
-- conductance network `randomEnvironmentConductance W`. Their branch resistances are exactly the
-- source-facing Solomon series `R_w^-` and `R_w^+`, so the Chapter 19 effective resistance is the
-- reciprocal of the sum of the branch conductances.
/-- Via the environment-to-conductance bridge, the Chapter 19 effective resistance from `0` to
infinity is the parallel combination of the source series `R_w^-` and `R_w^+` for an elliptic
environment, stated directly under the canonical RWRE owner from Definition 19.34. -/
theorem randomEnvironment_effectiveResistanceToInfinity_eq_parallel
    (hW : W.IsElliptic) :
    effectiveResistanceToInfinity (randomEnvironmentConductance W) P X 0 =
      ((R⁻[W])⁻¹ + (R⁺[W])⁻¹)⁻¹ := sorry

section DirectionalEscape

-- Proof sketch: approximate the two-point boundary `{−N, N}` and use the finite-interval exit
-- formula for a one-dimensional RWRE. Passing to the limit yields Solomon's textbook ratio
-- `R_w^+ / (R_w^- + R_w^+)`, interpreted with Solomon's convention `∞ / ∞ = 1`.
/-- Theorem 19.33 (1): for an elliptic environment, if `R_w^- < ∞` or `R_w^+ < ∞`, then the
probability that the walk started from `0` tends to `-∞` is
`R_w^+ / (R_w^- + R_w^+)`, with Solomon's convention `∞ / ∞ = 1`. -/
theorem randomEnvironmentWalk_prob_tendsToNegInfinity
    (hW : W.IsElliptic)
    (hfinite : R⁻[W] < ∞ ∨ R⁺[W] < ∞) :
    (P 0 : Measure Ω) {ω | Tendsto (fun n ↦ X n ω) atTop atBot} =
      solomonDirectionalSeriesRatio R⁺[W] R⁻[W] := sorry

-- Proof sketch: the same finite-interval computation, now for exiting at `+N`, gives Solomon's
-- complementary ratio `R_w^- / (R_w^- + R_w^+)`, again with the convention `∞ / ∞ = 1`.
/-- Theorem 19.33 (2): for an elliptic environment, if `R_w^- < ∞` or `R_w^+ < ∞`, then the
probability that the walk started from `0` tends to `+∞` is
`R_w^- / (R_w^- + R_w^+)`, with Solomon's convention `∞ / ∞ = 1`. -/
theorem randomEnvironmentWalk_prob_tendsToPosInfinity
    (hW : W.IsElliptic)
    (hfinite : R⁻[W] < ∞ ∨ R⁺[W] < ∞) :
    (P 0 : Measure Ω) {ω | Tendsto (fun n ↦ X n ω) atTop atTop} =
      solomonDirectionalSeriesRatio R⁻[W] R⁺[W] := sorry

end DirectionalEscape

section Oscillation

variable
  (hleft : R⁻[W] = ∞)
  (hright : R⁺[W] = ∞)

-- Proof sketch: when both Solomon series diverge, the one-dimensional RWRE is recurrent. A
-- recurrent nearest-neighbor walk on `ℤ` visits arbitrarily negative states infinitely often, so
-- its pathwise `liminf` is `-∞`.
/-- Theorem 19.33 (3): if `R_w^- = ∞` and `R_w^+ = ∞`, then `liminf X_n = -∞` almost surely. -/
theorem randomEnvironmentWalk_ae_hasLiminfEqNegInfinity :
    ∀ᵐ ω ∂(P 0 : Measure Ω), liminf (fun n ↦ (((X n ω : ℤ) : ℝ) : EReal)) atTop = ⊥ := sorry

-- Proof sketch: under the same recurrent hypothesis, the walk also visits arbitrarily large
-- positive states infinitely often, hence `limsup X_n = +∞`.
/-- Theorem 19.33 (4): if `R_w^- = ∞` and `R_w^+ = ∞`, then `limsup X_n = +∞` almost surely. -/
theorem randomEnvironmentWalk_ae_hasLimsupEqPosInfinity :
    ∀ᵐ ω ∂(P 0 : Measure Ω), limsup (fun n ↦ (((X n ω : ℤ) : ℝ) : EReal)) atTop = ⊤ := sorry

end Oscillation

end RWRERealization

end ProbabilityTheory
