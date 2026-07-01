import Mathlib
import AchimKlenkeLean.Items.Chap02.Definition_2_14
import AchimKlenkeLean.Items.Chap05.Definition_5_22
import AchimKlenkeLean.Items.Chap21.Exercise_21_5_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

noncomputable section

universe u

namespace ProbabilityTheory

local notation "PathSpace" => C(BrownianBridgeTime, ℝ)

local instance pathSpaceMeasurableSpace : MeasurableSpace PathSpace := borel _

local instance pathSpaceBorelSpace : BorelSpace PathSpace := ⟨rfl⟩

local notation "W" => fun t (ω : PathSpace) ↦ ω t

/-- The coordinate process on `C([0,1], ℝ)` has almost surely continuous sample paths under every
measure, because continuity is built into the path-space carrier. -/
private theorem hasAlmostSurelyContinuousPaths_pathCoordinateProcess
    (μ : Measure PathSpace) :
    HasAlmostSurelyContinuousPaths μ W := by
  filter_upwards with ω
  simpa [HasAlmostSurelyContinuousPaths, processPath] using ω.continuous

-- The owner abstraction here is `IsBrownianBridge` for the coordinate process `W` on path space.

variable {Ω : Type u}

/-- The empirical bridge process `Gₙ` from Exercise 21.8.1, written with Lean's `0`-based
indexing as the centered empirical cdf process built from the first `n + 1` transformed
uniforms. -/
def empiricalBridgeProcess (U : ℕ → Ω → Set.Icc (0 : ℝ) 1) (n : ℕ)
    (t : BrownianBridgeTime) : Ω → ℝ :=
  fun ω ↦
    Real.sqrt (n + 1 : ℝ) *
      (empiricalDistributionFunction (fun (i : Fin (n + 1)) ω ↦ (U i.1 ω : ℝ)) ω t - (t : ℝ))

-- Proof sketch: this is just the defining finite-sum formula for `Gₙ`, with Lean's `n + 1`
-- convention replacing the textbook's `n`.
/-- Expanding `empiricalBridgeProcess U n t ω` gives the normalized centered empirical sum. -/
theorem empiricalBridgeProcess_def
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1) (n : ℕ) (t : BrownianBridgeTime) (ω : Ω) :
    empiricalBridgeProcess U n t ω =
      (Real.sqrt (n + 1 : ℝ))⁻¹ *
        ∑ i : Fin (n + 1), ((if (U i.1 ω : ℝ) ≤ (t : ℝ) then 1 else 0) - (t : ℝ)) := by
  rw [empiricalBridgeProcess, empiricalDistributionFunction_apply]
  have hN : (n + 1 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hsqrt : Real.sqrt (n + 1 : ℝ) ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 (by positivity)
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp [Fintype.card_fin, nsmul_eq_mul]
  field_simp [hN, hsqrt]
  rw [Real.sq_sqrt (by positivity)]

/-- The Kolmogorov--Smirnov statistic `Mₙ = ‖Gₙ‖∞` attached to the empirical bridge process. -/
noncomputable def empiricalBridgeSupStatistic
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ sSup (Set.range fun t : BrownianBridgeTime ↦ |empiricalBridgeProcess U n t ω|)

-- Proof sketch: unfold the definition; the statistic is the supremum over `[0,1]` of the
-- absolute value of the empirical bridge sample path.
/-- Expanding `empiricalBridgeSupStatistic U n ω` gives the supremum of `|Gₙ(t,ω)|` over
`t ∈ [0,1]`. -/
theorem empiricalBridgeSupStatistic_def
    (U : ℕ → Ω → Set.Icc (0 : ℝ) 1) (n : ℕ) (ω : Ω) :
    empiricalBridgeSupStatistic U n ω =
      sSup (Set.range fun t : BrownianBridgeTime ↦ |empiricalBridgeProcess U n t ω|) :=
  rfl

/-- The explicit piecewise-linear smoothing kernel suggested for `hₙ` in Exercise 21.8.1. -/
def empiricalBridgeSmoothingKernel (ε : ℕ → ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  1 - min (max (s / ε n) 0) 1

/-- The centering term `gₙ(t) = ∫₀¹ hₙ(u - t) du`, namely the expectation of the smoothed
indicator `hₙ(U - t)` for `U ∼ Unif[0,1]`. -/
noncomputable def empiricalBridgeSmoothingCenter (ε : ℕ → ℝ) (n : ℕ)
    (t : BrownianBridgeTime) : ℝ :=
  ∫ u in Set.Icc (0 : ℝ) 1, empiricalBridgeSmoothingKernel ε n (u - (t : ℝ)) ∂volume

/-- The continuous centered approximation `Hₙ` to `Gₙ`, built from the smoothed indicator kernel
`hₙ` and centered by the matching uniform mean `gₙ`. -/
noncomputable def smoothedEmpiricalBridgeProcess
    (ε : ℕ → ℝ) (U : ℕ → Ω → Set.Icc (0 : ℝ) 1) (n : ℕ)
    (t : BrownianBridgeTime) : Ω → ℝ :=
  fun ω ↦
    (Real.sqrt (n + 1 : ℝ))⁻¹ *
      ∑ i : Fin (n + 1),
        (empiricalBridgeSmoothingKernel ε n ((U i.1 ω : ℝ) - (t : ℝ)) -
          empiricalBridgeSmoothingCenter ε n t)

-- Proof sketch: for fixed `ω`, each summand `t ↦ hₙ(Uᵢ(ω) - t)` is piecewise affine on `[0,1]`,
-- hence continuous, and the centering term `gₙ(t) = ∫₀¹ hₙ(u - t) du` is continuous as an
-- integral of the same kernel orientation.
-- Finite sums preserve continuity.
/-- The smoothed empirical bridge has continuous sample paths on `[0,1]`. -/
theorem continuous_smoothedEmpiricalBridgeProcess
    (ε : ℕ → ℝ) (U : ℕ → Ω → Set.Icc (0 : ℝ) 1) (n : ℕ) (ω : Ω) :
    Continuous (fun t : BrownianBridgeTime ↦ smoothedEmpiricalBridgeProcess ε U n t ω) := sorry

/-- The `n`th smoothed empirical bridge sample path, viewed as a continuous map on `[0,1]`. -/
noncomputable def smoothedEmpiricalBridgePath
    (ε : ℕ → ℝ) (U : ℕ → Ω → Set.Icc (0 : ℝ) 1) (n : ℕ) (ω : Ω) :
    PathSpace :=
  ⟨fun t ↦ smoothedEmpiricalBridgeProcess ε U n t ω,
    continuous_smoothedEmpiricalBridgeProcess ε U n ω⟩

-- Proof sketch: `smoothedEmpiricalBridgePath` was defined by bundling the sample path of
-- `smoothedEmpiricalBridgeProcess` as a continuous map, so evaluating it recovers the original
-- process value.
/-- Evaluating the bundled smoothed path at time `t` recovers the smoothed empirical bridge. -/
theorem smoothedEmpiricalBridgePath_apply
    (ε : ℕ → ℝ) (U : ℕ → Ω → Set.Icc (0 : ℝ) 1) (n : ℕ) (ω : Ω)
    (t : BrownianBridgeTime) :
    smoothedEmpiricalBridgePath ε U n ω t = smoothedEmpiricalBridgeProcess ε U n t ω :=
  rfl

variable [MeasurableSpace Ω]

section EmpiricalBridge

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : ℕ → Ω → Set.Icc (0 : ℝ) 1}

-- Proof sketch: each summand `1_[0,t](U_i) - t` has expectation `0` because `U_i` is uniform on
-- `[0,1]`; linearity of expectation then gives the centered empirical sum expectation `0`.
/-- Exercise 21.8.1 (1): for the transformed uniforms `Uᵢ = F(Xᵢ)`, every empirical bridge
marginal `Gₙ(t)` is centered. -/
theorem empiricalBridgeProcess_mean_zero
    (hU_iid : IsIID U μ)
    (hU_uniform :
      ∀ t : BrownianBridgeTime,
        μ {ω | (U 0 ω : ℝ) ≤ (t : ℝ)} = ENNReal.ofReal (t : ℝ))
    (n : ℕ) (t : BrownianBridgeTime) :
    ∫ ω, empiricalBridgeProcess U n t ω ∂μ = 0 := sorry

-- Proof sketch: expand the covariance of the normalized sum. Independence kills the off-diagonal
-- terms, and the remaining variance of the Bernoulli indicator `1_[0,t](U_0)` gives
-- `P[U_0 ≤ s ∧ t] - P[U_0 ≤ s] P[U_0 ≤ t] = min(s,t) - st`.
/-- Exercise 21.8.1 (2): the covariance kernel of the empirical bridge process is
`Cov[Gₙ(s), Gₙ(t)] = min(s,t) - st`. -/
theorem empiricalBridgeProcess_covariance
    (hU_iid : IsIID U μ)
    (hU_uniform :
      ∀ t : BrownianBridgeTime,
        μ {ω | (U 0 ω : ℝ) ≤ (t : ℝ)} = ENNReal.ofReal (t : ℝ))
    (n : ℕ) (s t : BrownianBridgeTime) :
    cov[empiricalBridgeProcess U n s, empiricalBridgeProcess U n t; μ] =
      brownianBridgeCovariance s t := sorry

-- Proof sketch: the increment is a normalized sum of centered Bernoulli differences. Expand the
-- fourth power, use independence and the uniform one-dimensional law to bound the resulting mixed
-- moments by a universal constant times `(t - s)^2 + |t - s| / (n + 1)`.
/-- Exercise 21.8.1 (3): there is a universal fourth-moment bound for increments of the empirical
bridge process. -/
theorem empiricalBridgeProcess_increment_fourthMoment_bound
    (hU_iid : IsIID U μ)
    (hU_uniform :
      ∀ t : BrownianBridgeTime,
        μ {ω | (U 0 ω : ℝ) ≤ (t : ℝ)} = ENNReal.ofReal (t : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ∀ s t : BrownianBridgeTime,
        ∫ ω, (empiricalBridgeProcess U n t ω - empiricalBridgeProcess U n s ω) ^ (4 : ℕ) ∂μ ≤
          C * (((t : ℝ) - (s : ℝ)) ^ (2 : ℕ) + |(t : ℝ) - (s : ℝ)| / (n + 1 : ℝ)) := sorry

section SmoothedApproximation

variable {ε : ℕ → ℝ}

-- Proof sketch: the fourth-moment estimate gives tightness on `C([0,1], ℝ)` for the centered
-- smoothed paths `Hₙ`. Their finite-dimensional distributions converge to those of a Brownian
-- bridge, and the limit law is therefore the law of the canonical coordinate process under some
-- Brownian-bridge path measure.
/-- Exercise 21.8.1 (4): for the explicit centered smoothed approximation `Hₙ` built from `hₙ`
and `gₙ`,
the path-valued random variables converge weakly on `C([0,1], ℝ)` to a Brownian bridge law. -/
theorem smoothedEmpiricalBridgePath_tendstoInDistribution_brownianBridge
    (hU_iid : IsIID U μ)
    (hU_uniform :
      ∀ t : BrownianBridgeTime,
        μ {ω | (U 0 ω : ℝ) ≤ (t : ℝ)} = ENNReal.ofReal (t : ℝ))
    (hε_pos : ∀ n : ℕ, 0 < ε n)
    (hε_tendsto : Tendsto ε atTop (𝓝 0)) :
    ∃ P : ProbabilityMeasure PathSpace,
      IsBrownianBridge (P : Measure PathSpace) W ∧
      TendstoInDistribution
        (fun n ω ↦ smoothedEmpiricalBridgePath ε U n ω)
        atTop
        id
        (fun _ ↦ μ)
        (P : Measure PathSpace) := sorry

end SmoothedApproximation

-- Proof sketch: use the weak convergence of the centered smoothed continuous approximants from
-- clause `(4)` and the continuity of the supremum functional on `C([0,1], ℝ)`. The difference
-- between `Mₙ = ‖Gₙ‖∞` and the corresponding smoothed supremum tends to `0`, so the continuous
-- mapping theorem yields the Kolmogorov--Smirnov limit law.
/-- Exercise 21.8.1 (5): the Kolmogorov--Smirnov statistics `Mₙ = ‖Gₙ‖∞` converge in
distribution to `M = sup_{t ∈ [0,1]} |B_t|` for a Brownian bridge `B`. -/
theorem empiricalBridgeSupStatistic_tendstoInDistribution_brownianBridgeSup
    (hU_iid : IsIID U μ)
    (hU_uniform :
      ∀ t : BrownianBridgeTime,
        μ {ω | (U 0 ω : ℝ) ≤ (t : ℝ)} = ENNReal.ofReal (t : ℝ)) :
    ∃ P : ProbabilityMeasure PathSpace,
      IsBrownianBridge (P : Measure PathSpace) W ∧
      TendstoInDistribution
        (fun n ↦ empiricalBridgeSupStatistic U n)
        atTop
        (fun ω : PathSpace ↦ ‖ω‖)
        (fun _ ↦ μ)
        (P : Measure PathSpace) := sorry

end EmpiricalBridge

end ProbabilityTheory
