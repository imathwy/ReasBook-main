

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_10_2_1 (from Items/Chap10) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u

section

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ mΩ} [SigmaFiniteFiltration μ ℱ]
variable {X : ℕ → Ω → ℝ} {τ : Ω → ℕ}

/-
Exercise 10.2.1 is `source-facing`: it records the stopped identities for the canonical square
variation from Example 10.2. The owner abstraction in the chapter is
`ProbabilityTheory.IsSquareVariationProcess`, while the canonical bridge/view is
`predictablePart_sq_isSquareVariationProcess`. Since the source refers to the canonical square
variation itself rather than an arbitrary square-variation witness, the main statements stay
formulated with the predictable compensator of the squared process.
-/
local notation "τ∞" => fun ω ↦ (τ ω : ℕ∞)
local notation "squareProcess" => fun n ω ↦ (X n ω) ^ 2
local notation "squareVariation" => predictablePart squareProcess ℱ μ

-- Proof sketch: apply optional sampling to the square-integrable martingale
-- `fun n ω ↦ X n ω ^ 2 - predictablePart squareProcess ℱ μ n ω`, use the integrability
-- of the stopped predictable part to justify taking expectations at the finite stopping time `τ`,
-- and rearrange the resulting identity to isolate the second moment of `X_τ - X_0`.
/-- Exercise 10.2.1 (1): Part (i), if the stopped canonical square variation `⟨X⟩_τ` is
integrable, then the expected squared increment of the martingale up to the finite stopping time
`τ` equals the expectation of the stopped square variation. -/
theorem expectation_stopped_sq_sub_eq_expectation_stopped_squareVariation
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) (hAτ : Integrable (stoppedValue squareVariation τ∞) μ) :
    μ[fun ω ↦ (stoppedValue X τ∞ ω - X 0 ω) ^ 2] = μ[stoppedValue squareVariation τ∞] := sorry

-- Proof sketch: use the same stopped-square-variation argument as in clause (1) to obtain
-- uniform integrability of the stopped martingale, then apply optional stopping for finite
-- stopping times to conclude that the expectation is preserved.
/-- Exercise 10.2.1 (2): Part (i), under the same integrability hypothesis on `⟨X⟩_τ`, the
expected value of the martingale at the finite stopping time `τ` agrees with the initial
expectation. -/
theorem expectation_stopped_martingale_eq_initial_of_squareVariation_integrable
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) (hAτ : Integrable (stoppedValue squareVariation τ∞) μ) :
    μ[stoppedValue X τ∞] = μ[X 0] := sorry

end

-- Proof sketch: construct a square-integrable martingale on a filtered probability space together
-- with a finite stopping time whose stopped square variation is not integrable; then compute the
-- two sides of the identities in (10.7) and verify that neither equality holds in that example.
/-- Exercise 10.2.1 (3): Part (ii), if the stopped square variation fails to be integrable, then
there exists a square-integrable martingale and a finite stopping time for which both identities
from `(10.7)` fail. -/
theorem exists_counterexample_stopped_squareVariation_nonintegrable :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ℱ : Filtration ℕ mΩ) (_ : SigmaFiniteFiltration μ ℱ)
      (X : ℕ → Ω → ℝ) (τ : Ω → ℕ),
        let tauInf : Ω → ℕ∞ := fun ω ↦ (τ ω : ℕ∞)
        let squareVariation : ℕ → Ω → ℝ := predictablePart (fun n ω ↦ (X n ω) ^ 2) ℱ μ
        Martingale X ℱ μ ∧
          (∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ) ∧
          IsStoppingTime ℱ tauInf ∧
          ¬ Integrable (stoppedValue squareVariation tauInf) μ ∧
          μ[fun ω ↦ (stoppedValue X tauInf ω - X 0 ω) ^ 2] ≠
            μ[stoppedValue squareVariation tauInf] ∧
          μ[stoppedValue X tauInf] ≠ μ[X 0] := sorry

/-! ### Example_10_2 (from Items/Chap10) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} {m0 : MeasurableSpace Ω}
variable {μ : Measure Ω} {ℱ : Filtration ℕ m0}

section

variable {X : ℕ → Ω → ℝ}

local notation "squareProcess" => fun n ω ↦ (X n ω) ^ 2

-- Proof sketch: apply the canonical Doob decomposition construction to the squared process
-- `n ↦ X n ^ 2`. Its predictable part is predictable and starts at `0`, while the compensated
-- process `X_n^2 - ⟨X⟩_n` is the canonical martingale part of the squared process.
/-- For a square-integrable discrete-time martingale `X`, subtracting the canonical square
variation `⟨X⟩` from the squared process yields a martingale. -/
theorem square_sub_squareVariation_martingale [SigmaFiniteFiltration μ ℱ]
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) :
    Martingale (fun n ω ↦ X n ω ^ 2 - (⟨X⟩[ℱ, μ]) n ω) ℱ μ := by
  have hSquare_adapted : Adapted ℱ squareProcess := by
    change Adapted ℱ (fun n ω ↦ (X n ω) ^ 2)
    simpa [pow_two] using
      (hX.stronglyAdapted.mul hX.stronglyAdapted).adapted
  rcases canonical_doobDecomposition hSquare_adapted hXsq with
    ⟨-, -, hMartingale, -⟩
  simpa [martingalePart] using hMartingale

-- Proof sketch: combine the canonical owner facts `squareVariation_zero`,
-- `squareVariation_predictable`, and `square_sub_squareVariation_martingale`.
/-- Example 10.2: for a square-integrable discrete-time martingale `X`, the canonical square
variation `⟨X⟩` realizes the textbook square-variation process of `X`. -/
theorem squareVariation_isSquareVariationProcess [SigmaFiniteFiltration μ ℱ]
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) :
    IsSquareVariationProcess ℱ μ X (⟨X⟩[ℱ, μ]) := by
  exact ⟨squareVariation_zero, squareVariation_predictable,
    square_sub_squareVariation_martingale hX hXsq⟩

end

/-! ### Exercise_10_2_2 (from Items/Chap10) -/
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
