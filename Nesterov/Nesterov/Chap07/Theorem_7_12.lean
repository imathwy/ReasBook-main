import Mathlib
import Nesterov.Chap07.Algorithm_7_10
import Nesterov.Chap07.Definition_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped MatrixGameRelativeScaleNotation StandardSimplex

variable {m n : ℕ+}

local notation "Δₙ" => Δ[(n : ℕ)]
local notation "PosMat" => { G : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ // Matrix.PosDef G }
local notation "DiagPosMat" =>
  { G : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ // Matrix.IsDiag G ∧ Matrix.PosDef G }
local notation "Solver" =>
  (Δₙ → ℝ) → ℝ → Set Δₙ → PosMat → Δₙ → ℕ → Δₙ

/- Theorem 7.12 lies in Chapter 7's nonnegative matrix-game / relative-scale outer-iteration
domain.

Sampled owner-style declarations:
- `Δ[n]` in `Chap06/Definition_6_11.lean`, the chapter simplex owner for finite matrix-game
  iterates;
- `matrixGameRelativeScaleIterate`, `matrixGameRelativeScaleTerminates`,
  `matrixGameRelativeScaleStoppingTime`, and `matrixGameRelativeScaleStoppingTime_min` in
  `Algorithm_7_10.lean`, the canonical owner API for the outer orbit and first accepted stage;
- `matrixGameRelativeScaleBlockLength` in `Algorithm_7_10.lean`, the canonical per-stage
  lower-level budget;
- `iterativeSmoothingTotalLowerLevelSteps` and the split statement surface in
  `Theorem_7_11.lean`, the nearby Chapter 7 pattern for stopping-time and total-work bounds;
- `IsRelativeAccuracy` in `Definition_7_1.lean`, the chapter owner for terminal relative-value
  accuracy.

Best owner abstraction:
- source-facing: Theorem 7.12's stopping-time, terminal-value, and total-work bounds for the
  nonnegative matrix-game relative-scale method;
- core/canonical: the Algorithm 7.10 owners
  `matrixGameRelativeScaleIterate m S f fμ D δ`,
  `matrixGameRelativeScaleStoppingTime hTerminate`,
  `matrixGameRelativeScaleOutputPoint hTerminate`, and
  `matrixGameRelativeScaleBlockLength m n δ`;
- bridge/view: the derived total lower-level work
  `matrixGameRelativeScaleTotalLowerLevelSteps hTerminate`.

Primitive data:
- the objective `f`, smoothing family `fμ`, diagonal positive-definite matrix data `D`,
  parameter `δ`, lower-level solver `S`, and canonical termination witness `hTerminate`;
- feasibility of the generated orbit, the feasible-set lower bound for `fStar`, the positivity
  regimes `0 < fStar` and `0 < δ`, the initial-value bound, and the terminal relative-gap
  estimate.

Derived API:
- the generated points `\hat x_t`;
- the stopping time `T`;
- the accepted output point `\hat x_T`;
- the total lower-level work up to `T`;
- the optional `IsRelativeAccuracy` packaging of the terminal-value conclusion.

Source/core/bridge triage:
- source-facing: the three atomic theorem clauses below;
- core/canonical: the Algorithm 7.10 orbit, stopping-time, and block-length owners;
- bridge/view: `matrixGameRelativeScaleTotalLowerLevelSteps`.
-/

/-- The total number of lower-level steps used by Algorithm 7.10 up to its canonical stopping
time, assuming that each outer stage uses the canonical block length
`matrixGameRelativeScaleBlockLength m n δ`. -/
def matrixGameRelativeScaleTotalLowerLevelSteps
    {S : Solver} {f : Δₙ → ℝ} {fμ : ℝ → Δₙ → ℝ} {D : DiagPosMat} {δ : ℝ}
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ) : ℕ :=
  matrixGameRelativeScaleStoppingTime hTerminate *
    matrixGameRelativeScaleBlockLength m n δ

-- Proof sketch: unfold `matrixGameRelativeScaleTotalLowerLevelSteps`.
/-- Expanding `matrixGameRelativeScaleTotalLowerLevelSteps hTerminate` gives the product of the
canonical stopping time and the canonical per-stage lower-level work budget. -/
theorem matrixGameRelativeScaleTotalLowerLevelSteps_def
    {S : Solver} {f : Δₙ → ℝ} {fμ : ℝ → Δₙ → ℝ} {D : DiagPosMat} {δ : ℝ}
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ) :
    matrixGameRelativeScaleTotalLowerLevelSteps hTerminate =
      matrixGameRelativeScaleStoppingTime hTerminate *
        matrixGameRelativeScaleBlockLength m n δ := sorry

section Complexity

variable
  {S : Solver} {f : Δₙ → ℝ} {fμ : ℝ → Δₙ → ℝ} {D : DiagPosMat}
  {δ fStar : ℝ} {feasibleSet : Set Δₙ}

local notation "x̂" => x̂[m; S; f; fμ; D | δ]

-- Proof sketch: use `matrixGameRelativeScaleStoppingTime_min hTerminate` to get geometric decay
-- before the accepted stage, evaluate feasibility at the generated points via
-- `hGenerated_feasible`, compare `f*` with the preterminal objective value, and combine this
-- with the initial estimate `f (x̂ 0) ≤ 2 √n fStar`.
/-- Theorem 7.12 (1): if every generated point `\hat x_t` is feasible, feasible points have
objective value at least `f*`, and the initial value satisfies `f(\hat x_0) ≤ 2 √n f*`, then
the stopping time satisfies `T ≤ 1 + log (2 √n)`. -/
theorem matrixGameRelativeScale_stoppingTime_le
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ)
    (hGenerated_feasible : ∀ t : ℕ, x̂ t ∈ feasibleSet)
    (hOptimal_value_le_of_feasible :
      ∀ (x : Δₙ) (_hx : x ∈ feasibleSet), fStar ≤ f x)
    (hfStar_pos : 0 < fStar)
    (hInitial_value_le :
      f (x̂ 0) ≤ 2 * Real.sqrt (n : ℝ) * fStar) :
    (matrixGameRelativeScaleStoppingTime hTerminate : ℝ) ≤
      1 + Real.log (2 * Real.sqrt (n : ℝ)) := sorry

-- Proof sketch: multiply the terminal relative-gap estimate by `1 + δ`, use `0 < 1 + δ`, and
-- rearrange the resulting inequality to isolate `f x̂T`.
/-- Theorem 7.12 (2): the accepted output point satisfies
`f(\hat x_T) ≤ (1 + δ) f*` once `δ > 0` and the terminal relative-gap estimate from the
relative-scale analysis is available. -/
theorem matrixGameRelativeScale_outputPoint_value_le
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ)
    (hδ : 0 < δ)
    (hTerminal_relative_gap :
      f (matrixGameRelativeScaleOutputPoint hTerminate) - fStar ≤
        (δ / (1 + δ)) * f (matrixGameRelativeScaleOutputPoint hTerminate)) :
    f (matrixGameRelativeScaleOutputPoint hTerminate) ≤ (1 + δ) * fStar := sorry

-- Proof sketch: combine Theorem 7.12 (1) with the definition of
-- `matrixGameRelativeScaleTotalLowerLevelSteps` as the product of the canonical stopping time and
-- the canonical block length, then expand the block-length formula.
/-- Theorem 7.12 (3): the total number of lower-level steps does not exceed
`4 e (1 + log (2 √n)) √(2 n log m) (1 + 1 / δ)` under the same feasibility and initial-value
hypotheses together with `δ > 0`. -/
theorem matrixGameRelativeScale_totalLowerLevelSteps_le
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ)
    (hδ : 0 < δ)
    (hGenerated_feasible : ∀ t : ℕ, x̂ t ∈ feasibleSet)
    (hOptimal_value_le_of_feasible :
      ∀ (x : Δₙ) (_hx : x ∈ feasibleSet), fStar ≤ f x)
    (hfStar_pos : 0 < fStar)
    (hInitial_value_le :
      f (x̂ 0) ≤ 2 * Real.sqrt (n : ℝ) * fStar) :
    (matrixGameRelativeScaleTotalLowerLevelSteps hTerminate : ℝ) ≤
      4 * Real.exp 1 * (1 + Real.log (2 * Real.sqrt (n : ℝ))) *
        Real.sqrt (2 * (n : ℝ) * Real.log (m : ℝ)) * (1 + 1 / δ) := sorry

-- Proof sketch: package the lower and upper bounds on `f x̂T` together with `0 < fStar` into the
-- three conjuncts defining `IsRelativeAccuracy`.
/-- If the optimal value `f*` is positive and the accepted output value is already known to lie
between `f*` and `(1 + δ) f*`, then the output value in Theorem 7.12 has relative accuracy `δ`
in the sense of Definition 7.1. -/
theorem matrixGameRelativeScale_outputPoint_isRelativeAccuracy
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ)
    (hfStar_pos : 0 < fStar)
    (hOutput_value_ge : fStar ≤ f (matrixGameRelativeScaleOutputPoint hTerminate))
    (hOutput_value_le :
      f (matrixGameRelativeScaleOutputPoint hTerminate) ≤ (1 + δ) * fStar) :
    IsRelativeAccuracy fStar δ (f (matrixGameRelativeScaleOutputPoint hTerminate)) := sorry

end Complexity
