import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_45 (from Items/Chap21) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The textbook Laplace transform of the generation-size variable `Z_n` in the critical geometric
branching process started from `i`. -/
noncomputable def criticalGeometricBranchingLaplaceTransform (n i : ℕ) : ℝ → ℝ :=
  fun t ↦
    ((((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n]) (Real.exp (-t))) ^ i)

/-- Evaluating `criticalGeometricBranchingLaplaceTransform` expands to the explicit iterate of the
critical geometric offspring pgf. -/
theorem criticalGeometricBranchingLaplaceTransform_apply (n i : ℕ) (t : ℝ) :
    criticalGeometricBranchingLaplaceTransform n i t =
      (((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n]) (Real.exp (-t))) ^ i :=
  rfl

/-- The generation-size variable `Z_n` has the textbook Laplace transform of the critical
geometric branching process started from `i` under the probability law `P`. -/
def HasCriticalGeometricBranchingLaplaceTransform
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) (i n : ℕ) : Prop :=
  ∀ t : ℝ,
    0 ≤ t →
      ∫ ω, Real.exp (-(t * (Z n ω : ℝ))) ∂(P : Measure Ω) =
        criticalGeometricBranchingLaplaceTransform n i t

/-- Unfolding `HasCriticalGeometricBranchingLaplaceTransform` gives the explicit Laplace-transform
identity. -/
theorem hasCriticalGeometricBranchingLaplaceTransform_iff
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) (i n : ℕ) :
    HasCriticalGeometricBranchingLaplaceTransform P Z i n ↔
      ∀ t : ℝ,
        0 ≤ t →
          ∫ ω, Real.exp (-(t * (Z n ω : ℝ))) ∂(P : Measure Ω) =
            criticalGeometricBranchingLaplaceTransform n i t :=
  Iff.rfl

-- Proof sketch: differentiate the Laplace-transform identity from the branching-process setup
-- `k` times at `λ = 0`, move the factor `(-1)^k` through the derivatives of
-- `exp (-(λ Z_n))`, and then evaluate at `0`.
/-- Lemma 21.45 (1): the `k`th moment of `Z_n` is obtained from the signed `k`th derivative at
`0` of the explicit Laplace transform
`λ ↦ ((((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n]) (e^{-λ}))^i)`. -/
theorem criticalGeometricBranching_moment_eq_signed_iteratedDeriv_at_zero
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) (k : ℕ) :
    moment (fun ω ↦ (Z n ω : ℝ)) k (P : Measure Ω) =
      (-1 : ℝ) ^ k * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) 0 := sorry

-- Proof sketch: specialize
-- `criticalGeometricBranching_moment_eq_signed_iteratedDeriv_at_zero` to `k = 1`, rewrite the
-- iterate of `probabilityGeneratingFunctionReal criticalGeometricOffspringPMF` with
-- Lemma 21.44, and evaluate the resulting first derivative at `0`.
/-- Lemma 21.45 (2): the first moment of `Z_n` is `i`. -/
theorem criticalGeometricBranching_first_moment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    moment (fun ω ↦ (Z n ω : ℝ)) 1 (P : Measure Ω) = i := sorry

-- Proof sketch: apply the derivative identity from clause (1) with `k = 2`, rewrite the pgf
-- iterate using Lemma 21.44, and simplify the resulting quadratic polynomial.
/-- The second moment of `Z_n` is `2in + i²`. -/
theorem criticalGeometricBranching_second_moment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    moment (fun ω ↦ (Z n ω : ℝ)) 2 (P : Measure Ω) =
      2 * (i : ℝ) * (n : ℝ) + (i : ℝ) ^ 2 := sorry

-- Proof sketch: apply clause (1) with `k = 3` and evaluate the third derivative of the explicit
-- rational form obtained from Lemma 21.44.
/-- The third moment of `Z_n` is `6in² + 6i²n + i³`. -/
theorem criticalGeometricBranching_third_moment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    moment (fun ω ↦ (Z n ω : ℝ)) 3 (P : Measure Ω) =
      6 * (i : ℝ) * (n : ℝ) ^ 2 + 6 * (i : ℝ) ^ 2 * (n : ℝ) + (i : ℝ) ^ 3 := sorry

-- Proof sketch: evaluate clause (1) at `k = 4` after rewriting the pgf iterate by
-- Lemma 21.44, then collect coefficients.
/-- The fourth moment of `Z_n` is `24in³ + 36i²n² + (12i³ + 2i)n + i⁴`. -/
theorem criticalGeometricBranching_fourth_moment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    moment (fun ω ↦ (Z n ω : ℝ)) 4 (P : Measure Ω) =
      24 * (i : ℝ) * (n : ℝ) ^ 3 + 36 * (i : ℝ) ^ 2 * (n : ℝ) ^ 2 +
        (12 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) + (i : ℝ) ^ 4 := sorry

-- Proof sketch: evaluate clause (1) at `k = 5` and simplify the resulting polynomial after the
-- Lemma 21.44 rewrite.
/-- The fifth moment of `Z_n` is
`120in⁴ + 240i²n³ + (120i³ + 30i)n² + (20i⁴ + 10i²)n + i⁵`. -/
theorem criticalGeometricBranching_fifth_moment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    moment (fun ω ↦ (Z n ω : ℝ)) 5 (P : Measure Ω) =
      120 * (i : ℝ) * (n : ℝ) ^ 4 + 240 * (i : ℝ) ^ 2 * (n : ℝ) ^ 3 +
        (120 * (i : ℝ) ^ 3 + 30 * (i : ℝ)) * (n : ℝ) ^ 2 +
        (20 * (i : ℝ) ^ 4 + 10 * (i : ℝ) ^ 2) * (n : ℝ) + (i : ℝ) ^ 5 := sorry

-- Proof sketch: evaluate clause (1) at `k = 6`, use Lemma 21.44 to rewrite the Laplace
-- transform, and collect the coefficients of the resulting sixth-degree polynomial.
/-- The sixth moment of `Z_n` is
`720in⁵ + 1800i²n⁴ + (1200i³ + 360i)n³ + (300i⁴ + 240i²)n² +
(30i⁵ + 30i³ + 2i)n + i⁶`. -/
theorem criticalGeometricBranching_sixth_moment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    moment (fun ω ↦ (Z n ω : ℝ)) 6 (P : Measure Ω) =
      720 * (i : ℝ) * (n : ℝ) ^ 5 + 1800 * (i : ℝ) ^ 2 * (n : ℝ) ^ 4 +
        (1200 * (i : ℝ) ^ 3 + 360 * (i : ℝ)) * (n : ℝ) ^ 3 +
        (300 * (i : ℝ) ^ 4 + 240 * (i : ℝ) ^ 2) * (n : ℝ) ^ 2 +
        (30 * (i : ℝ) ^ 5 + 30 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) +
        (i : ℝ) ^ 6 := sorry

section PopulationMartingale

variable {P : ProbabilityMeasure Ω} {Z : ℕ → Ω → ℕ}

local notation "Zℝ" => fun n ω ↦ (Z n ω : ℝ)
local notation "Pμ" => (P : Measure Ω)
variable (hZ_sm : ∀ n, StronglyMeasurable (Zℝ n))
local notation "ℱZ" => Filtration.natural Zℝ hZ_sm

-- Proof sketch: verify integrability and strong measurability of the real-valued population
-- process, then use the critical branching conditional-expectation identity
-- `E[Z_{n+1} | 𝓕_n] = Z_n` with respect to the natural filtration and apply the canonical
-- discrete-time martingale constructor `martingale_nat`.
/-- Lemma 21.45 (3): under the one-step critical branching conditional-expectation identity, the
population process `Z` is a martingale with respect to its natural filtration. -/
theorem criticalGeometricBranching_population_martingale
    (hZ_int : ∀ n, Integrable (Zℝ n) Pμ)
    (h_step : ∀ n, Pμ[Zℝ (n + 1) | ℱZ n] =ᵐ[Pμ] Zℝ n) :
    Martingale Zℝ ℱZ Pμ :=
  let h_step' : ∀ n, Pμ[Zℝ (n + 1) | ℱZ n] =ᵐ[Pμ] fun ω ↦ (1 : ℝ) * Zℝ n ω :=
    fun n ↦ by simpa using h_step n
  by
    simpa [branchingNormalizedProcess] using
      branchingNormalizedProcess_martingale (μ := Pμ) (Z := Zℝ) (m := 1) zero_lt_one hZ_sm
        hZ_int h_step'

end PopulationMartingale

-- Proof sketch: every probability measure has vanishing first central moment.
/-- The first central moment of `Z_n` is `0`. -/
theorem criticalGeometricBranching_first_centralMoment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) (n : ℕ) :
    centralMoment (fun ω ↦ (Z n ω : ℝ)) 1 (P : Measure Ω) = 0 := by
  simpa using
    (centralMoment_one :
      centralMoment (fun ω ↦ (Z n ω : ℝ)) 1 (P : Measure Ω) = 0)

-- Proof sketch: use the first-moment identity to identify the mean with `i`, expand
-- `centralMoment`, and substitute the explicit second raw moment formula.
/-- Lemma 21.45 (4): the second central moment of `Z_n` is `2in`. -/
theorem criticalGeometricBranching_second_centralMoment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    centralMoment (fun ω ↦ (Z n ω : ℝ)) 2 (P : Measure Ω) =
      2 * (i : ℝ) * (n : ℝ) := sorry

-- Proof sketch: expand the third central moment in terms of raw moments, use the first-moment
-- identity to rewrite the mean as `i`, and simplify.
/-- The third central moment of `Z_n` is `6in²`. -/
theorem criticalGeometricBranching_third_centralMoment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    centralMoment (fun ω ↦ (Z n ω : ℝ)) 3 (P : Measure Ω) =
      6 * (i : ℝ) * (n : ℝ) ^ 2 := sorry

-- Proof sketch: expand the fourth central moment via the binomial formula and substitute the raw
-- moment identities from clause (2).
/-- The fourth central moment of `Z_n` is `24in³ + 12i²n² + 2in`. -/
theorem criticalGeometricBranching_fourth_centralMoment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    centralMoment (fun ω ↦ (Z n ω : ℝ)) 4 (P : Measure Ω) =
      24 * (i : ℝ) * (n : ℝ) ^ 3 + 12 * (i : ℝ) ^ 2 * (n : ℝ) ^ 2 +
        2 * (i : ℝ) * (n : ℝ) := sorry

-- Proof sketch: express the fifth central moment in terms of raw moments and simplify using the
-- formulas from clause (2).
/-- The fifth central moment of `Z_n` is `120in⁴ + 120i²n³ + 30in²`. -/
theorem criticalGeometricBranching_fifth_centralMoment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    centralMoment (fun ω ↦ (Z n ω : ℝ)) 5 (P : Measure Ω) =
      120 * (i : ℝ) * (n : ℝ) ^ 4 + 120 * (i : ℝ) ^ 2 * (n : ℝ) ^ 3 +
        30 * (i : ℝ) * (n : ℝ) ^ 2 := sorry

-- Proof sketch: expand the sixth central moment in terms of raw moments and collect the
-- remaining polynomial terms after substitution.
/-- The sixth central moment of `Z_n` is
`720in⁵ + 1080i²n⁴ + (120i³ + 360i)n³ + 60i²n² + 2in`. -/
theorem criticalGeometricBranching_sixth_centralMoment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    centralMoment (fun ω ↦ (Z n ω : ℝ)) 6 (P : Measure Ω) =
      720 * (i : ℝ) * (n : ℝ) ^ 5 + 1080 * (i : ℝ) ^ 2 * (n : ℝ) ^ 4 +
        (120 * (i : ℝ) ^ 3 + 360 * (i : ℝ)) * (n : ℝ) ^ 3 +
        60 * (i : ℝ) ^ 2 * (n : ℝ) ^ 2 + 2 * (i : ℝ) * (n : ℝ) := sorry

end ProbabilityTheory
