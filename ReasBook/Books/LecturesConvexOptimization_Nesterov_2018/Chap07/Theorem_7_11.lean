import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap07.Algorithm_7_9
import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {m : ℕ+} {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "PosMat" => { G : Matrix (Fin n) (Fin n) ℝ // Matrix.PosDef G }
local notation "ConstraintVec" => { d : E // d ≠ 0 }

/- Theorem 7.11 lies in the chapter's relative-scale minimax / recursive outer-iterate /
first-stopping-time domain.

Sampled owner-style declarations:
- `iterativeSmoothingParameter`, `iterativeSmoothingStoppingTime`, and
  `iterativeSmoothingOutputPoint` in `Algorithm_7_9.lean`;
- `iterativeSmoothingBlockLength` in `Algorithm_7_9.lean`, the canonical owner of the per-stage
  lower-level work budget;
- `relativeScaleSubgradientApproximationTotalLowerLevelSteps` in `Theorem_7_3.lean` and
  `schemeSNRestartingTotalLowerLevelSteps` in `Theorem_7_5.lean`, the nearby chapter pattern for
  deriving total lower-level work from canonical stopping data;
- `IsRelativeAccuracy` in `Definition_7_1.lean`, the chapter owner for the terminal relative
  accuracy conclusion.

Best owner abstraction:
- source-facing: Theorem 7.11's stopping-time, terminal-value, and total-work bounds for the
  Algorithm 7.9 relative-scale scheme;
- core/canonical: the Algorithm 7.9 owners
  `xHat : ℕ → E`, `iterativeSmoothingParameter a δ`,
  `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)`,
  `iterativeSmoothingStoppingTime hTerminate`, and
  `iterativeSmoothingBlockLength (m : ℕ) n δ γ`;
- bridge/view: the derived total lower-level work
  `iterativeSmoothingTotalLowerLevelSteps δ γ hTerminate`.

Primitive data:
- the lower-level subroutine `S`, the family `a`, and the geometric data `d : ConstraintVec`
  and `G`;
- an explicit Algorithm 7.9 outer iterate `xHat` together with the auxiliary hypotheses that it
  starts at `x₀`, has positive stagewise smoothing parameters, and satisfies the recursive update
  rule;
- the termination witness `hTerminate` for the canonical first accepted outer stage;
- the feasible-set lower bound, the feasibility of the generated canonical orbit, the initial
  objective bound, and the terminal relative-gap estimate.

Derived API:
- the recursive orbit `x̂_t`;
- the smoothing parameter at stage `t`, namely
  `iterativeSmoothingParameter a δ (xHat t)`;
- the textbook stopping time `T`;
- the accepted output point `\hat x_T`;
- the total lower-level work up to `T`.

Source/core/bridge triage:
- source-facing: the three bounds asserted by Theorem 7.11;
- core/canonical: the Algorithm 7.9 iterate, smoothing, stopping-time, and output owners;
- bridge/view: the total-work product `T * \tilde N`.

This file now uses the refined source-facing owner directly: the explicit outer iterate `xHat`,
with the stagewise positivity and recursive update information kept as ordinary hypotheses rather
than hidden behind a typeclass wrapper, together with the canonical stopping-time API derived from
that iterate.
-/

/-- The total number of lower-level steps used by Algorithm 7.9 up to its canonical stopping
time, assuming that each outer stage uses the canonical block length
`iterativeSmoothingBlockLength (m : ℕ) n δ γ`. -/
def iterativeSmoothingTotalLowerLevelSteps
    (δ γ : ℝ) {a : Fin (m : ℕ) → E} {xHat : ℕ → E}
    (hTerminate : iterativeSmoothingTerminates a xHat) : ℕ :=
  iterativeSmoothingStoppingTime hTerminate *
    iterativeSmoothingBlockLength (m : ℕ) n δ γ

/-- Expanding `iterativeSmoothingTotalLowerLevelSteps δ γ hTerminate` gives the product of the
canonical stopping time and the canonical block length. -/
theorem iterativeSmoothingTotalLowerLevelSteps_def
    (δ γ : ℝ) {a : Fin (m : ℕ) → E} {xHat : ℕ → E}
    (hTerminate : iterativeSmoothingTerminates a xHat) :
    iterativeSmoothingTotalLowerLevelSteps δ γ hTerminate =
      iterativeSmoothingStoppingTime hTerminate *
        iterativeSmoothingBlockLength (m : ℕ) n δ γ :=
  rfl

section Complexity

variable
  {S : (E → ℝ) → ℝ → Set E → PosMat → E → ℕ → E}
  {a : Fin (m : ℕ) → E} {d : ConstraintVec} {G : PosMat}
  {δ γ fStar : ℝ} {feasibleSet : Set E} {xHat : ℕ → E}

variable
  (hZero : xHat 0 = iterativeSmoothingInitialPoint d G)
  (hParameterPos : ∀ t : ℕ, 0 < iterativeSmoothingParameter a δ (xHat t))
  (hSucc :
    ∀ t : ℕ,
      xHat (t + 1) =
        iterativeSmoothingStep S a d G δ γ (xHat t) (hParameterPos t))

variable (hTerminate : iterativeSmoothingTerminates a xHat)

local notation "x̂" => xHat
local notation "F" => maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|)
local notation "s" => iterativeSmoothingStoppingIndex hTerminate
local notation "T" => iterativeSmoothingStoppingTime hTerminate
local notation "x̂T" => iterativeSmoothingOutputPoint hTerminate

-- Proof sketch: for every `t < iterativeSmoothingStoppingIndex hTerminate`,
-- `iterativeSmoothingStoppingIndex_min hTerminate` gives
-- `F (x̂ (t + 1)) < (1 / e) * F (x̂ t)`, so the canonical orbit decays geometrically before the
-- accepted stage. Compare the feasible preterminal iterate `x̂ s` with `fStar`, combine this with
-- the initial estimate `F (x̂ 0) ≤ γ √n fStar`, and obtain
-- `(T : ℝ) ≤ 1 + log (γ √n)`.
/-- Theorem 7.11 (1): the stopping time is bounded by `1 + log (γ √n)` once the scale parameter
is positive. -/
theorem iterativeSmoothing_stoppingTime_le
    (hScale_pos : 0 < γ * Real.sqrt (n : ℝ))
    (hPreterminal_feasible : x̂ s ∈ feasibleSet)
    (hOptimal_value_le_of_feasible :
      ∀ (x : E) (_hx : x ∈ feasibleSet), fStar ≤ F x)
    (hInitial_value_le :
      F (x̂ 0) ≤ γ * Real.sqrt (n : ℝ) * fStar) :
    (T : ℝ) ≤ 1 + Real.log (γ * Real.sqrt (n : ℝ)) := sorry

-- Proof sketch: multiply the terminal relative-gap estimate by `1 + δ`, use `0 < 1 + δ`, and
-- rearrange the resulting linear inequality to isolate `F x̂T`.
/-- Theorem 7.11 (2): the accepted output point satisfies
`f(\hat x_T) ≤ (1 + δ) f*` in the positive-`δ` regime. -/
theorem iterativeSmoothing_outputPoint_value_le
    (hδ : 0 < δ)
    (hTerminal_relative_gap :
      F x̂T - fStar ≤ (δ / (1 + δ)) * F x̂T) :
    F x̂T ≤ (1 + δ) * fStar := sorry

-- Proof sketch: combine the stopping-time bound from Theorem 7.11 (1) with the definition of
-- `iterativeSmoothingTotalLowerLevelSteps` as the product of the canonical stopping time and the
-- canonical block length, then expand the block-length expression.
/-- Theorem 7.11 (3): the total number of lower-level steps is bounded by the stated explicit
complexity expression once the scale parameter and relative-accuracy parameter are in their
textbook range. -/
theorem iterativeSmoothing_totalLowerLevelSteps_le
    (hδ : 0 < δ)
    (hScale_pos : 0 < γ * Real.sqrt (n : ℝ))
    (hPreterminal_feasible : x̂ s ∈ feasibleSet)
    (hOptimal_value_le_of_feasible :
      ∀ (x : E) (_hx : x ∈ feasibleSet), fStar ≤ F x)
    (hInitial_value_le :
      F (x̂ 0) ≤ γ * Real.sqrt (n : ℝ) * fStar) :
    (iterativeSmoothingTotalLowerLevelSteps δ γ hTerminate : ℝ) ≤
      2 * γ * Real.exp 1 * (1 + Real.log (γ * Real.sqrt (n : ℝ))) *
        Real.sqrt (2 * (n : ℝ) * Real.log (2 * (m : ℝ))) * (1 + 1 / δ) := sorry

/-- If the optimal value `f*` is positive, then the accepted output point in Theorem 7.11 has
relative accuracy `δ` with respect to `f*` in the sense of Definition 7.1. -/
theorem iterativeSmoothing_outputPoint_isRelativeAccuracy
    (hfStar_pos : 0 < fStar)
    (hδ : 0 < δ)
    (hOutput_value_ge : fStar ≤ F (iterativeSmoothingOutputPoint hTerminate))
    (hTerminal_relative_gap :
      F (iterativeSmoothingOutputPoint hTerminate) - fStar ≤
        (δ / (1 + δ)) * F (iterativeSmoothingOutputPoint hTerminate)) :
    IsRelativeAccuracy fStar δ (F (iterativeSmoothingOutputPoint hTerminate)) := by
  have hOne_add_δ : 0 < 1 + δ := by
    linarith
  have hMul :
      (F (iterativeSmoothingOutputPoint hTerminate) - fStar) * (1 + δ) ≤
        δ * F (iterativeSmoothingOutputPoint hTerminate) := by
    have hScaled :=
      mul_le_mul_of_nonneg_right hTerminal_relative_gap hOne_add_δ.le
    have hOne_add_δ_ne : (1 + δ) ≠ 0 := ne_of_gt hOne_add_δ
    simpa [div_eq_mul_inv, hOne_add_δ_ne, mul_assoc, mul_left_comm, mul_comm] using hScaled
  have hUpper : F (iterativeSmoothingOutputPoint hTerminate) ≤ (1 + δ) * fStar := by
    nlinarith [hMul]
  exact ⟨hfStar_pos, hOutput_value_ge, hUpper⟩

end Complexity
