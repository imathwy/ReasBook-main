import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap10.Definition_10_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The multiplicative process associated with a sequence `(Y_n)` of real random variables,
with `X₀ = 1` and `X_{n+1} = X_n Y_{n+1}`. -/
def multiplicativeProcess (Y : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ ↦ 1
  | n + 1 => fun ω ↦ multiplicativeProcess Y n ω * Y (n + 1) ω

-- Proof sketch: unfold the recursive definition at time `0`.
/-- The multiplicative process starts from the constant value `1`. -/
@[simp] theorem multiplicativeProcess_zero (Y : ℕ → Ω → ℝ) :
    multiplicativeProcess Y 0 = fun _ ↦ 1 := sorry

-- Proof sketch: unfold the recursive definition at time `n + 1`.
/-- The multiplicative process satisfies the one-step recursion `X_{n+1} = X_n Y_{n+1}`. -/
@[simp] theorem multiplicativeProcess_succ (Y : ℕ → Ω → ℝ) (n : ℕ) :
    multiplicativeProcess Y (n + 1) =
      fun ω ↦ multiplicativeProcess Y n ω * Y (n + 1) ω := sorry

-- Proof sketch: prove by induction on `n`, using that products of measurable real-valued
-- random variables are measurable.
/-- If the factors `Y₁, Y₂, …` are measurable, then every stage of the multiplicative process is
measurable. -/
theorem measurable_multiplicativeProcess {Y : ℕ → Ω → ℝ}
    (hY : ∀ n, Measurable (Y (n + 1))) :
    ∀ n, Measurable (multiplicativeProcess Y n) := sorry

-- Proof sketch: combine `measurable_multiplicativeProcess` with the standard fact that measurable
-- real-valued maps are strongly measurable.
/-- If the factors `Y₁, Y₂, …` are measurable, then every stage of the multiplicative process is
strongly measurable. This is the bridge from the source-facing process recursion to the canonical
owner filtration `Filtration.natural`. -/
theorem stronglyMeasurable_multiplicativeProcess {Y : ℕ → Ω → ℝ}
    (hY : ∀ n, Measurable (Y (n + 1))) :
    ∀ n, StronglyMeasurable (multiplicativeProcess Y n) := sorry

/-- The textbook square-variation process from Example 10.7 for the multiplicative martingale
`X_n = ∏_{i=1}^n Y_i`, namely
`⟨X⟩_n = ∑_{i=0}^{n-1} Var[Y_{i+1}; μ] X_i^2`. -/
noncomputable def multiplicativeProcessSquareVariation (Y : ℕ → Ω → ℝ) (μ : Measure Ω) :
    ℕ → Ω → ℝ :=
  fun n ω ↦ ∑ i ∈ Finset.range n, Var[Y (i + 1); μ] * (multiplicativeProcess Y i ω) ^ 2

@[simp] theorem multiplicativeProcessSquareVariation_zero (Y : ℕ → Ω → ℝ) (μ : Measure Ω) :
    multiplicativeProcessSquareVariation Y μ 0 = fun _ ↦ 0 := by
  ext ω
  simp [multiplicativeProcessSquareVariation]

section

variable [IsProbabilityMeasure μ]
variable {Y : ℕ → Ω → ℝ} (hY : ∀ n, Measurable (Y (n + 1)))

local notation "X" => multiplicativeProcess Y
local notation "ℱ" => Filtration.natural X (stronglyMeasurable_multiplicativeProcess hY)

-- Proof sketch: use the natural filtration of `X`, identify `X_n` as `ℱ n`-measurable by
-- construction, and combine independence of `Y_{n+1}` from the past with
-- `μ[Y_{n+1}] = 1` and the recursion `X_{n+1} = X_n Y_{n+1}`.
/-- Under independence and unit mean, the multiplicative process is a martingale with respect to
the natural filtration `σ(X)` of the process itself. The hypotheses are imposed only on the
actual factor sequence `Y₁, Y₂, …` used in the recursion. -/
theorem multiplicativeProcess_martingale (hYind : iIndepFun (fun n ↦ Y (n + 1)) μ)
    (hYmean : ∀ n, μ[Y (n + 1)] = 1) :
    Martingale X ℱ μ := sorry

end

-- Proof sketch: use induction on `n` and the multiplicative recursion, combining independence on a
-- probability space with the product formula for second moments of independent nonnegative random
-- variables.
/-- If the factors `Y₁, Y₂, …` are independent and square integrable on a probability space, then
every stage of the multiplicative process is square integrable. -/
theorem multiplicativeProcess_memLp_two {Y : ℕ → Ω → ℝ}
    [IsProbabilityMeasure μ] (hYind : iIndepFun (fun n ↦ Y (n + 1)) μ)
    (hY2 : ∀ n, MemLp (Y (n + 1)) 2 μ) :
    ∀ n, MemLp (multiplicativeProcess Y n) 2 μ := sorry

section

variable [IsProbabilityMeasure μ]
variable {Y : ℕ → Ω → ℝ} (hY : ∀ n, Measurable (Y (n + 1)))

local notation "X" => multiplicativeProcess Y
local notation "ℱ" => Filtration.natural X (stronglyMeasurable_multiplicativeProcess hY)
local notation "A" => multiplicativeProcessSquareVariation Y μ

-- Proof sketch: rewrite `X_{n+1} - X_n` as `(Y_{n+1} - 1) X_n`, pull out the
-- `ℱ_n`-measurable factor `X_n^2` from the conditional expectation, and identify the remaining
-- scalar with `Var[Y_{n+1}; μ]` using independence and `μ[Y_{n+1}] = 1`.
/-- The conditional second moment of the increment of the multiplicative martingale is the variance
of the new factor times the square of the previous stage. -/
theorem multiplicativeProcess_condExp_sq_increment
    (hYind : iIndepFun (fun n ↦ Y (n + 1)) μ)
    (hYmean : ∀ n, μ[Y (n + 1)] = 1) (hY2 : ∀ n, MemLp (Y (n + 1)) 2 μ) (n : ℕ) :
    μ[(fun ω ↦
        (X (n + 1) ω - X n ω) ^ 2) | ℱ n] =ᵐ[μ]
      fun ω ↦ Var[Y (n + 1); μ] * (X n ω) ^ 2 := sorry

-- Proof sketch: combine the martingale statement for `X`, square integrability of each `X n`,
-- and the explicit conditional-increment formula to verify the chapter's
-- `IsSquareVariationProcess` axioms for the source-facing process `A`.
/-- Example 10.7: if `(Y_n)` is an independent sequence of square-integrable real random variables
with `μ[Y_n] = 1`, then the explicit process
`⟨X⟩_n = ∑_{i=0}^{n-1} Var[Y_{i+1}; μ] X_i^2` is a square variation process of the multiplicative
martingale `X_n = ∏_{i=1}^n Y_i` with respect to the natural filtration `σ(X)`. -/
theorem multiplicativeProcessSquareVariation_isSquareVariationProcess
    (hYind : iIndepFun (fun n ↦ Y (n + 1)) μ)
    (hYmean : ∀ n, μ[Y (n + 1)] = 1) (hY2 : ∀ n, MemLp (Y (n + 1)) 2 μ) :
    IsSquareVariationProcess ℱ μ X A := sorry

-- Proof sketch: apply the generic bridge from any square-variation process to the canonical
-- predictable part of the squared process.
/-- At each fixed time, the canonical predictable part of the squared multiplicative martingale
agrees almost everywhere with the explicit textbook square-variation process from Example 10.7. -/
theorem multiplicativeProcess_predictablePart_ae_eq_squareVariation
    (hYind : iIndepFun (fun n ↦ Y (n + 1)) μ)
    (hYmean : ∀ n, μ[Y (n + 1)] = 1) (hY2 : ∀ n, MemLp (Y (n + 1)) 2 μ) (n : ℕ) :
    ⟨X⟩[ℱ, μ] n =ᵐ[μ] A n :=
  IsSquareVariationProcess.predictablePart_sq_ae_eq
    (multiplicativeProcessSquareVariation_isSquareVariationProcess hY hYind hYmean hY2)
    (fun k ↦ (multiplicativeProcess_memLp_two hYind hY2 k).integrable_sq)
    n

end
