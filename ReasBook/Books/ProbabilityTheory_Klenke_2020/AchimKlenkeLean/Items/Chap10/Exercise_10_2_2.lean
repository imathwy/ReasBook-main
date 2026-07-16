import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap10.Example_10_7
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap09.Example_9_13

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

noncomputable section

section

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The exponential martingale process attached to the increment sequence `Y` and parameter `θ`,
with the cumulant generating function `cgf (Y 0) μ` playing the role of the textbook map `ψ`. -/
def cramerLundbergExponentialProcess (Y : ℕ → Ω → ℝ) (μ : Measure Ω) (θ : ℝ) : ℕ → Ω → ℝ :=
  fun n ω ↦
    Real.exp
      (θ * partialSum Y n ω - (n : ℝ) * cgf (Y 0) μ θ)

/-- The textbook process `Z_n^θ` is given pointwise by the exponential tilt of the partial sums. -/
@[simp]
theorem cramerLundbergExponentialProcess_apply (Y : ℕ → Ω → ℝ) (μ : Measure Ω) (θ : ℝ)
    (n : ℕ) (ω : Ω) :
    cramerLundbergExponentialProcess Y μ θ n ω =
      Real.exp (θ * partialSum Y n ω - (n : ℝ) * cgf (Y 0) μ θ) :=
  rfl

/-- The normalized exponential increment factors whose multiplicative process recovers the
textbook Cramér-Lundberg exponential process. This is the bridge/view layer to the Chapter 10
owner abstraction `multiplicativeProcess`. -/
def cramerLundbergExponentialFactorProcess (Y : ℕ → Ω → ℝ) (μ : Measure Ω) (θ : ℝ) :
    ℕ → Ω → ℝ
  | 0 => fun _ ↦ 1
  | n + 1 => fun ω ↦ Real.exp (θ * Y n ω - cgf (Y 0) μ θ)

/-- The source-facing exponential process is the multiplicative process of the normalized
exponential increment factors. This is the bridge to the Chapter 10 multiplicative-process owner
abstraction. -/
theorem cramerLundbergExponentialProcess_eq_multiplicativeProcess
    (Y : ℕ → Ω → ℝ) (μ : Measure Ω) (θ : ℝ) :
    cramerLundbergExponentialProcess Y μ θ =
      multiplicativeProcess (cramerLundbergExponentialFactorProcess Y μ θ) := by
  funext n ω
  induction n with
  | zero =>
      simp [cramerLundbergExponentialProcess, partialSum]
  | succ n ih =>
      let c : ℝ := cgf (Y 0) μ θ
      have hsum : partialSum Y (n + 1) ω = partialSum Y n ω + Y n ω := by
        rw [partialSum_apply, partialSum_apply]
        simpa using (Finset.sum_range_succ (fun i : ℕ ↦ Y i ω) n)
      have hexp :
          Real.exp (θ * partialSum Y (n + 1) ω - ((n + 1 : ℕ) : ℝ) * c) =
            Real.exp (θ * partialSum Y n ω - (n : ℝ) * c) * Real.exp (θ * Y n ω - c) := by
        rw [hsum, Nat.cast_add, Nat.cast_one]
        have hsplit :
            θ * (partialSum Y n ω + Y n ω) - ((n : ℝ) + 1) * c =
              (θ * partialSum Y n ω - (n : ℝ) * c) + (θ * Y n ω - c) := by
          ring
        rw [hsplit, Real.exp_add]
      rw [cramerLundbergExponentialProcess, multiplicativeProcess_succ]
      rw [cramerLundbergExponentialFactorProcess]
      calc
        Real.exp (θ * partialSum Y (n + 1) ω - ((n + 1 : ℕ) : ℝ) * cgf (Y 0) μ θ) =
            Real.exp (θ * partialSum Y n ω - (n : ℝ) * c) * Real.exp (θ * Y n ω - c) := by
              simpa [c] using hexp
        _ =
            multiplicativeProcess (cramerLundbergExponentialFactorProcess Y μ θ) n ω *
              Real.exp (θ * Y n ω - cgf (Y 0) μ θ) := by
              simpa [c] using congrArg (fun x ↦ x * Real.exp (θ * Y n ω - c)) ih

/-- The ruin probability for initial capital `k₀`, written on a probability space as the
probability that the shifted partial-sum process ever becomes negative. -/
def ruinProbability (Y : ℕ → Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ] (k₀ : ℝ) : ℝ :=
  μ.real {ω | ∃ n : ℕ, partialSum Y n ω + k₀ < 0}

/-- The ruin probability is the real-valued probability of the event that the capital process
crosses below zero. -/
@[simp] theorem ruinProbability_def {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (k₀ : ℝ) :
    ruinProbability Y μ k₀ =
      μ.real {ω | ∃ n : ℕ, partialSum Y n ω + k₀ < 0} :=
  rfl

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {Y : ℕ → Ω → ℝ}
variable (hY_meas : ∀ n, Measurable (Y n))
variable {δ : ℝ}

local notation "S" => partialSum Y

private theorem partialSumStronglyMeasurable
    (hY_meas : ∀ n, Measurable (Y n)) (n : ℕ) : StronglyMeasurable (S n) :=
  (partialSum_measurable Y hY_meas n).stronglyMeasurable

local notation "ℱY" =>
  Filtration.natural S (partialSumStronglyMeasurable hY_meas)

/-- Exercise 10.2.2 (1): for every parameter `θ` in the exponential-moment interval, the process
`Z^θ` built from the partial sums is a martingale with respect to the natural filtration of the
partial-sum process. -/
-- Proof sketch: identify `Z^θ` with the multiplicative process of the normalized exponential
-- factors from `cramerLundbergExponentialProcess_eq_multiplicativeProcess`; the cgf normalization
-- makes each new factor have mean `1` at the fixed parameter `θ`, and independence of the next
-- increment from the past gives the one-step conditional-expectation identity on the natural
-- filtration of the partial sums.
theorem cramerLundbergExponentialProcess_martingale {θ : ℝ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ)
    (hθ : θ ∈ Set.Ioo (-δ) δ) :
    Martingale (cramerLundbergExponentialProcess Y μ θ) ℱY μ :=
  sorry

/-- Exercise 10.2.2 (2): the cumulant generating function of the increment law is strictly convex
on the interval where the exponential moments are finite. -/
-- Proof sketch: apply the strict convexity of the logarithmic moment-generating function on an
-- interval of exponential integrability, and use that the increment law is not almost surely
-- constant to rule out the affine case.
theorem cgf_strictConvexOn_increment_interval
    (hY_not_ae_const : ¬ ∃ c : ℝ, Y 0 =ᵐ[μ] fun _ ↦ c)
    (hY_exp_int : ∀ θ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ) :
    StrictConvexOn ℝ (Set.Ioo (-δ) δ) (cgf (Y 0) μ) := sorry

/-- Exercise 10.2.2 (3): for every nonzero parameter `θ` in the exponential-moment interval, the
expectations `E[√(Z_n^θ)]` decay to `0`. -/
-- Proof sketch: rewrite `√(Z_n^θ)` as an exponential martingale term with parameter `θ / 2`,
-- compute its expectation using independence and identical distribution, and then use strict
-- convexity of the cumulant generating function to obtain exponential decay for `θ ≠ 0`; the
-- interval condition for `θ / 2` is automatic from `hθ`.
theorem expectation_sqrt_cramerLundbergExponentialProcess_tendsto_zero {θ : ℝ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_not_ae_const : ¬ ∃ c : ℝ, Y 0 =ᵐ[μ] fun _ ↦ c)
    (hY_exp_int : ∀ ϑ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) μ)
    (hθ : θ ∈ Set.Ioo (-δ) δ) (hθ_ne : θ ≠ 0) :
    Filter.Tendsto
      (fun n ↦ μ[fun ω ↦ Real.sqrt (cramerLundbergExponentialProcess Y μ θ n ω)])
      Filter.atTop (nhds 0) := sorry

/-- Exercise 10.2.2 (4): for every nonzero parameter `θ` in the exponential-moment interval, the
process `Z_n^θ` converges almost surely to `0`. -/
-- Proof sketch: combine the martingale property and nonnegativity of `Z^θ` with the decay of
-- `E[√(Z_n^θ)]`; convergence of the nonnegative martingale and the vanishing square-root moments
-- force the almost-sure limit to be zero. The midpoint condition for `θ / 2` is derived
-- internally from `hθ`, so it is not part of the public statement.
theorem cramerLundbergExponentialProcess_tendsto_zero_ae {θ : ℝ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_not_ae_const : ¬ ∃ c : ℝ, Y 0 =ᵐ[μ] fun _ ↦ c)
    (hY_exp_int : ∀ ϑ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (ϑ * Y 0 ω)) μ)
    (hθ : θ ∈ Set.Ioo (-δ) δ) (hθ_ne : θ ≠ 0) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n ↦ cramerLundbergExponentialProcess Y μ θ n ω) Filter.atTop (nhds 0) := sorry

/-- Exercise 10.2.2 (5): if the increment mean is positive and a nonzero root `θ⋆` of the
cumulant generating function exists, then that root is negative. -/
-- Proof sketch: `cgf (Y 0) μ 0 = 0`, the derivative at `0` is the positive mean of `Y_0`, and the
-- strict convexity of `cgf` shows that a second zero cannot lie to the right of `0`; the positive
-- mean together with the nonzero root already excludes the almost surely constant case.
theorem cgf_root_neg_of_mean_pos {θStar : ℝ}
    (hY_exp_int : ∀ θ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ)
    (hY_mean_pos : 0 < μ[Y 0]) (hθStar : θStar ∈ Set.Ioo (-δ) δ)
    (hroot : cgf (Y 0) μ θStar = 0) (hθStar_ne : θStar ≠ 0) :
    θStar < 0 := sorry

/-- Exercise 10.2.2 (6): if `θ⋆` is a nonzero root of the cumulant generating function and the
increment mean is positive, then the ruin probability is bounded by `exp (θ⋆ k₀)`. -/
-- Proof sketch: apply optional stopping to the nonnegative martingale `Z^{θ⋆}` stopped at the
-- ruin time and a deterministic truncation, use `cgf (Y 0) μ θ⋆ = 0` to simplify the stopped
-- process, and then pass to the limit to obtain the Cramér-Lundberg bound.
theorem ruinProbability_le_exp_cgf_root {θStar k₀ : ℝ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_exp_int : ∀ θ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (θ * Y 0 ω)) μ)
    (hY_mean_pos : 0 < μ[Y 0]) (hθStar : θStar ∈ Set.Ioo (-δ) δ)
    (hroot : cgf (Y 0) μ θStar = 0) (hθStar_ne : θStar ≠ 0) :
    ruinProbability Y μ k₀ ≤ Real.exp (θStar * k₀) := sorry

/-- Exercise 10.2.2 (7): in the special `±1`-valued case with integer initial capital, the
Cramér-Lundberg inequality is sharp, recovering the classical exact ruin formula with
`r = exp θ⋆`; because `ruinProbability` here records the event that the capital process becomes
strictly negative, the exact formula carries the expected one-step shift. -/
-- Proof sketch: specialize the stopped-exponential-martingale argument to the nearest-neighbor
-- random walk, where the required exponential moments are automatic, identify the stopped process
-- at ruin exactly, and solve the resulting two-point recursion to turn the upper bound into the
-- exact formula for hitting the negative half-line, equivalently for hit-`0` ruin after shifting
-- the initial capital from `k₀` to `k₀ + 1`.
theorem ruinProbability_eq_exp_cgf_root_of_two_point_steps {θStar : ℝ} {k₀ : ℕ}
    (hY_indep : iIndepFun Y μ) (hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ)
    (hY_mean_pos : 0 < μ[Y 0]) (hθStar : θStar ∈ Set.Ioo (-δ) δ)
    (hroot : cgf (Y 0) μ θStar = 0) (hθStar_ne : θStar ≠ 0)
    (h_two_point : ∀ n, ∀ᵐ ω ∂μ, Y n ω = -1 ∨ Y n ω = 1) :
    ruinProbability Y μ k₀ = Real.exp (θStar * ((k₀ : ℝ) + 1)) := sorry

end
