import ProbabilityTheory_Klenke_2020.Chap05.Theorem_5_36
import ProbabilityTheory_Klenke_2020.Chap17.Theorem_17_25
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/-- The square-rate pure-birth `Q`-matrix from Remark 17.26, written on Lean's `ℕ` by adjoining a
dummy row at `0`: for every positive state `n`, the only off-diagonal jump is `n → n + 1` with
rate `n^2`, the diagonal entry is `-n^2`, and all other entries vanish. -/
def squareRatePureBirthQMatrix : ℕ → ℕ → ℝ :=
  fun n m ↦
    (n : ℝ)^2 * ((if m = n + 1 then (1 : ℝ) else 0) - (if m = n then (1 : ℝ) else 0))

-- Proof sketch: in row `n`, the indicator of the successor state is `1` at `n + 1`, while the
-- diagonal indicator vanishes there.
/-- In row `n`, the successor jump in `squareRatePureBirthQMatrix` has rate `n^2`. -/
theorem squareRatePureBirthQMatrix_succ (n : ℕ) :
    squareRatePureBirthQMatrix n (n + 1) = (n : ℝ)^2 := by
  simp [squareRatePureBirthQMatrix]

-- Proof sketch: in row `n`, the successor indicator vanishes at `n` and the diagonal indicator is
-- `1`, leaving exactly the coefficient `-n^2`.
/-- In row `n`, the diagonal entry of `squareRatePureBirthQMatrix` is `-n^2`. -/
theorem squareRatePureBirthQMatrix_self (n : ℕ) :
    squareRatePureBirthQMatrix n n = -(n : ℝ)^2 := by
  simp [squareRatePureBirthQMatrix]

-- Proof sketch: each row is the scalar multiple `(n : ℝ)^2` of the difference of the successor
-- point mass and the diagonal point mass, so the off-diagonal sign condition is immediate and the
-- row sum is `1 - 1 = 0`.
/-- The square-rate pure-birth generator is a `Q`-matrix. -/
instance instIsQMatrixSquareRatePureBirthQMatrix : IsQMatrix squareRatePureBirthQMatrix where
  offDiag_nonneg := by
    intro n m hnm
    by_cases hsucc : m = n + 1
    · simp [squareRatePureBirthQMatrix, hsucc]
    · have hself : m ≠ n := by
        simpa [eq_comm] using hnm
      simp [squareRatePureBirthQMatrix, hsucc, hself]
  row_hasSum_zero := by
    intro n
    simpa [squareRatePureBirthQMatrix] using
      (HasSum.mul_left ((n : ℝ)^2)
        (HasSum.sub (hasSum_ite_eq (n + 1) (1 : ℝ)) (hasSum_ite_eq n (1 : ℝ))))

section

variable {Ω : Type u}

/-- The source-facing path from Remark 17.26, written with the chapter owner `arrivalTime`: at
time `t`, the state is the largest level `n + 1` whose arrival time is at most `t`; if infinitely
many levels have already been reached by time `t`, the path takes the cemetery value `⊤`. -/
def squareRatePureBirthPath (T : ℕ → Ω → ℝ) (t : NNReal) : Ω → WithTop ℕ :=
  fun ω ↦
    sSup {m | ∃ n : ℕ, m = (n + 1 : WithTop ℕ) ∧ arrivalTime T n ω ≤ (t : ℝ)}

/-- The `ℕ`-valued version of the square-rate pure-birth path started from the state `x`, with
`0` as the cemetery state matching the dummy row of `squareRatePureBirthQMatrix`. For `x = n + 1`
it is obtained by shifting the waiting-time family to `T n, T (n + 1), …` and translating the
resulting positive levels back by `n`; explosion is sent to `0`. -/
def squareRatePureBirthStateFrom (T : ℕ → Ω → ℝ) (x : ℕ) (t : NNReal) : Ω → ℕ :=
  fun ω ↦
    match x with
    | 0 => 0
    | n + 1 =>
        match squareRatePureBirthPath (fun k ω' ↦ T (n + k) ω') t ω with
        | ⊤ => 0
        | (m : ℕ) => n + m

/-- The explosion time of the square-rate pure-birth path, expressed as the supremum of its level
times in `ENNReal`. -/
def squareRatePureBirthExplosionTime (T : ℕ → Ω → ℝ) : Ω → ENNReal :=
  fun ω ↦ iSup fun n : ℕ ↦ ENNReal.ofReal (arrivalTime T n ω)

end

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (T : ℕ → Ω → ℝ)

-- Proof sketch: starting from `x = n + 1`, the path waits an exponential time of rate `(n + 1)^2`
-- before the first jump, because the shifted family `k ↦ T (n + k)` has the correct first law;
-- the memoryless property together with `iIndepFun` then yields the textbook small-time
-- transition asymptotics `P_x[X_t = x + 1] = x^2 t + o(t)`, `P_x[X_t = x] = 1 - x^2 t + o(t)`,
-- and `P_x[X_t = y] = o(t)` for all other `y`.
/-- Under independent waiting-time laws `T n ∼ Exp((n + 1)^2)`, the explicit construction started
from `x` has the singleton right-derivative transition limits prescribed by
`squareRatePureBirthQMatrix`. This is the source-facing transition-limit form of the infinitesimal
generator statement. -/
theorem squareRatePureBirthStateFrom_transition_limit
    (hT_indep : iIndepFun T P)
    (hT_law : ∀ n : ℕ, HasLaw (T n) (expMeasure ((n + 1 : ℝ)^2)) P)
    (x y : ℕ) :
    Filter.Tendsto
      (fun t : NNReal ↦
        (((P.map (squareRatePureBirthStateFrom T x t)).real {y}) - (Measure.dirac x).real {y}) /
          (t : ℝ))
      (nhdsWithin (0 : NNReal) (Set.Ioi 0))
      (nhds (squareRatePureBirthQMatrix x y)) := sorry

-- Proof sketch: package the transition laws
-- `κ t x := (P : Measure Ω).map (squareRatePureBirthStateFrom T x t)` as a kernel family on the
-- discrete state space `ℕ`, then apply `squareRatePureBirthStateFrom_transition_limit` rowwise.
/-- The explicit pure-birth construction yields a kernel family whose owner generator predicate is
`HasGeneratorMatrix squareRatePureBirthQMatrix`. This is the thin bridge from the source-facing
waiting-time model to the chapter's canonical generator API. -/
theorem exists_squareRatePureBirthKernel_hasGeneratorMatrix
    (hT_indep : iIndepFun T P)
    (hT_law : ∀ n : ℕ, HasLaw (T n) (expMeasure ((n + 1 : ℝ)^2)) P) :
    ∃ κ : NNReal → Kernel ℕ ℕ,
      HasGeneratorMatrix κ squareRatePureBirthQMatrix ∧
        ∀ t : NNReal, ∀ x : ℕ, κ t x = P.map (squareRatePureBirthStateFrom T x t) := sorry

-- Proof sketch: the level times are increasing partial sums of nonnegative exponential waiting
-- times, so monotone convergence identifies the explosion time with the limit of those partial
-- sums; the expectations are the convergent series `∑ 1 / (n + 1)^2`.
/-- The explosion time of the square-rate pure-birth path has finite expectation under the
exponential waiting-time laws from Remark 17.26. -/
theorem squareRatePureBirthExplosionTime_lintegral_lt_top
    (hT_law : ∀ n : ℕ, HasLaw (T n) (expMeasure ((n + 1 : ℝ)^2)) P) :
    ∫⁻ ω, squareRatePureBirthExplosionTime T ω ∂P < ∞ := sorry

-- Proof sketch: each level time is a finite sum of waiting times, so its expectation is the sum
-- of the exponential means `1 / (k + 1)^2`; the previous finite-expectation result then forces the
-- explosion time to be finite almost surely, which means that the path reaches `⊤` in finite time.
/-- Remark 17.26: if the waiting times `T n` have the laws `Exp((n + 1)^2)`, then the arrival time
of level `n + 1` has expectation `∑_{k=1}^n 1 / k^2`, and the associated explicit square-rate
pure-birth path explodes almost surely in finite time. -/
theorem squareRatePureBirth_expectedLevelTime_and_ae_explosion
    (hT_law : ∀ n : ℕ, HasLaw (T n) (expMeasure ((n + 1 : ℝ)^2)) P) :
    (∀ n : ℕ, P[arrivalTime T n] =
      ∑ k ∈ Finset.range n, 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) ∧
    ∀ᵐ ω ∂P, ∃ t : NNReal, squareRatePureBirthPath T t ω = ⊤ := sorry

end

end ProbabilityTheory
