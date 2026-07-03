import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_21_1 (from Items/Chap21) -/
open MeasureTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {I : Type v}
variable {E : Type w}

/-- Definition 21.1 (1): two stochastic processes are modifications, or versions, of each other
if for every time `t` the random variables `X t` and `Y t` agree almost surely. -/
abbrev AreModifications (μ : Measure Ω) (X Y : I → Ω → E) : Prop :=
  ∀ t : I, X t =ᵐ[μ] Y t

/-- Definition 21.1 (2): two stochastic processes are indistinguishable if there is a measurable
null set outside of which all time coordinates agree simultaneously. -/
def AreIndistinguishable (μ : Measure Ω) (X Y : I → Ω → E) : Prop :=
  ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧ ∀ t : I, {ω | X t ω ≠ Y t ω} ⊆ N

-- Proof sketch: if all disagreements are contained in one measurable null set `N`, then for each
-- fixed time `t` the disagreement event `{ω | X t ω ≠ Y t ω}` is also null, which is exactly
-- the almost-everywhere equality statement `X t =ᵐ[μ] Y t`.
/-- Indistinguishable processes are modifications of one another. -/
theorem areModifications_of_areIndistinguishable
    (μ : Measure Ω) (X Y : I → Ω → E) (hXY : AreIndistinguishable μ X Y) :
    AreModifications μ X Y := by
  rcases hXY with ⟨N, -, hN, hNsub⟩
  intro t
  rw [Filter.EventuallyEq, ae_iff]
  exact measure_mono_null (hNsub t) hN

end ProbabilityTheory

/-! ### Exercise_21_1_1 (from Items/Chap21) -/
open MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
variable {d : ℕ}

/-- A process has locally Hölder sample paths of exponent `γ` if every sample path is locally
Hölder of order `γ` on the Euclidean parameter space. -/
def HasLocallyHolderPaths (γ : ℝ≥0) (Y : EuclideanSpace ℝ (Fin d) → Ω → E) : Prop :=
  ∀ ω : Ω, ∀ x : EuclideanSpace ℝ (Fin d),
    ∃ s : Set (EuclideanSpace ℝ (Fin d)), s ∈ 𝓝 x ∧
      ∃ C : ℝ≥0, HolderOnWith C γ (fun t ↦ Y t ω) s

-- Proof sketch: apply the Kolmogorov--Chentsov argument on each cube `[-T,T]^d`, where the
-- increment estimate has exponent `d + β`, to obtain a `γ`-Hölder modification on that cube for
-- every `γ < β / α`. Then use consistency of the cube restrictions together with the modification
-- property to glue these local versions into one process on `ℝ^d` whose sample paths are locally
-- `γ`-Hölder everywhere.
/-- Exercise 21.1.1: under the multidimensional Kolmogorov--Chentsov moment bound from Remark
21.7 on every cube `[-T,T]^d`, a process indexed by `ℝ^d` admits a modification whose sample
paths are locally Hölder-continuous of every order `γ ∈ (0, β / α)`. -/
theorem exists_locallyHolderWith_version_of_euclidean_moment_bound
    (μ : Measure Ω) (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    {α β γ : ℝ≥0}
    (hα : 0 < α) (hβ : 0 < β)
    (hγ₀ : 0 < γ) (hγ : γ < β / α)
    (hMoment :
      ∀ T : ℝ, 0 < T →
        ∃ C : ℝ≥0, ∀ s t : EuclideanSpace ℝ (Fin d),
          (∀ i : Fin d, |s i| ≤ T) →
          (∀ i : Fin d, |t i| ≤ T) →
            ∫⁻ ω, edist (X t ω) (X s ω) ^ (α : ℝ) ∂μ ≤
              (C : ℝ≥0∞) * (ENNReal.ofReal ‖t - s‖) ^ (((d : ℝ≥0) + β : ℝ))) :
    ∃ Y : EuclideanSpace ℝ (Fin d) → Ω → E,
      (∀ t : EuclideanSpace ℝ (Fin d), X t =ᵐ[μ] Y t) ∧
        HasLocallyHolderPaths γ Y := sorry

end ProbabilityTheory

/-! ### Exercise_21_1_2 (from Items/Chap21) -/
open MeasureTheory

noncomputable section

universe u

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Exercise 21.1.2: for a real-valued process on nonnegative time with measurable time slices and
continuous sample paths, the sample-path interval integral over `[(a : ℝ), (b : ℝ)] ⊆ [0, ∞)` is a
measurable function of the sample point. -/
-- Proof sketch: first use
-- `stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable` to show that
-- `(t, ω) ↦ X (Real.toNNReal t) ω` is strongly measurable on `ℝ × Ω`; then apply measurability of
-- the Bochner integral in one variable over the restricted Lebesgue measure on `Ι a b`, and
-- rewrite the interval integral by `intervalIntegral.integral_of_le`.
theorem measurable_intervalIntegral_of_continuous_paths
    {X : NNReal → Ω → ℝ}
    (hX_meas : ∀ t, Measurable (X t))
    (hX_cont : ∀ ω, Continuous fun t ↦ X t ω)
    {a b : NNReal} (hab : a < b) :
    Measurable (fun ω ↦ ∫ t in (a : ℝ)..(b : ℝ), X (Real.toNNReal t) ω) := by
  let ν : Measure ℝ := volume.restrict (Set.uIoc (a : ℝ) (b : ℝ))
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  have h_cont : ∀ ω, Continuous fun t ↦ X (Real.toNNReal t) ω := fun ω ↦
    (hX_cont ω).comp continuous_real_toNNReal
  have h_uncurry : StronglyMeasurable (Function.uncurry fun t ω ↦ X (Real.toNNReal t) ω) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable h_cont
      (fun t ↦ (hX_meas (Real.toNNReal t)).stronglyMeasurable)
  have h_swap : StronglyMeasurable (Function.uncurry fun ω t ↦ X (Real.toNNReal t) ω) := by
    simpa [Function.uncurry] using h_uncurry.comp_measurable measurable_swap
  have h_integral : StronglyMeasurable (fun ω ↦ ∫ t, X (Real.toNNReal t) ω ∂ν) :=
    h_swap.integral_prod_right
  have h_eq :
      (fun ω ↦ ∫ t in (a : ℝ)..(b : ℝ), X (Real.toNNReal t) ω) =
        fun ω ↦ ∫ t, X (Real.toNNReal t) ω ∂ν := by
    ext ω
    simpa [ν, Set.uIoc_of_le habR] using
      (intervalIntegral.integral_of_le hab.le :
        ∫ t in (a : ℝ)..(b : ℝ), X (Real.toNNReal t) ω =
          ∫ t in Set.Ioc (a : ℝ) (b : ℝ), X (Real.toNNReal t) ω ∂volume)
  rw [h_eq]
  exact h_integral.measurable

end MeasureTheory

/-! ### Exercise_21_1_3 (from Items/Chap21) -/
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u}
variable {E : Type v} [TopologicalSpace E]

-- Proof sketch: fix a sample point `ω`. Along that path, the map `t ↦ min t (τ ω).untopA` is
-- right continuous, so composing the right-continuous path `t ↦ X t ω` with this time change
-- preserves right continuity.
/-- Exercise 21.1.3 (7): the stopped process of a right-continuous process is still right
continuous. -/
theorem stoppedProcess_hasRightContinuousPaths
    {X : NNReal → Ω → E} (hX_rc : HasRightContinuousPaths X) {τ : Ω → ENNReal} :
    HasRightContinuousPaths (stoppedProcess X τ) := sorry

variable [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {ℱ : Filtration NNReal mΩ} [SigmaFiniteFiltration μ ℱ]
variable {X Y : NNReal → Ω → ℝ}

/-- The dyadic ceiling approximation `t ↦ 2^{-n} ⌈2^n t⌉` applied pointwise to a nonnegative random
time. -/
def dyadicCeilApprox (n : ℕ) (τ : Ω → NNReal) : Ω → NNReal :=
  fun ω ↦
    ((Nat.ceil ((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ) : NNReal) /
      ((2 : NNReal) ^ n))

-- Proof sketch: for each deterministic time `t`, the event
-- `{dyadicCeilApprox n τ ≤ t}` can be rewritten as `{τ ≤ k / 2^n}` for the appropriate dyadic
-- predecessor of `t`; this is measurable because `τ` is a stopping time.
/-- The dyadic ceiling approximation of a finite nonnegative stopping time is again a stopping
time. -/
theorem dyadicCeilApprox_isStoppingTime {τ : Ω → NNReal}
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal)) (n : ℕ) :
    IsStoppingTime ℱ fun ω ↦ (dyadicCeilApprox n τ ω : ENNReal) := sorry

-- Proof sketch: the dyadic ceilings `σⁿ` decrease to `σ`, so the stopping-time σ-algebras
-- `𝓕_{σⁿ}` decrease to `𝓕_σ`; backward martingale convergence then gives both almost-sure and
-- `L¹` convergence of the conditional expectations of the fixed integrable random variable
-- `X_{τ^m}`.
/-- Exercise 21.1.3 (1): for fixed `m`, the conditional expectations of `X_{τ^m}` with respect to
the dyadic stopping-time σ-algebras `𝓕_{σ^n}` converge almost surely and in `L¹` to the
conditional expectation with respect to `𝓕_σ`. -/
theorem dyadic_condExp_stoppedValue_tendsto_of_bounded_stopping_times
    (hX : Supermartingale X ℱ μ)
    {σ τ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
    (hσ_bdd : ∃ T : NNReal, ∀ ω, σ ω ≤ T)
    (hτ_bdd : ∃ T : NNReal, ∀ ω, τ ω ≤ T) (m : ℕ) :
    (∀ᵐ ω ∂μ,
      Tendsto
        (fun n ↦
          μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
            (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω)
        atTop
        (𝓝
          (μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
            hσ.measurableSpace] ω))) ∧
      Tendsto
        (fun n ↦
          eLpNorm
            (μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
                (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] -
              μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
                hσ.measurableSpace])
            1 μ)
        atTop (𝓝 0) := sorry

-- Proof sketch: right continuity of the sample paths gives pointwise convergence
-- `X_{σ^n} → X_σ`, and boundedness of the stopping times upgrades the sampled family to a
-- uniformly integrable one, yielding convergence in `L¹`.
/-- Exercise 21.1.3 (2): the dyadic ceiling samples `X_{σ^n}` converge almost surely and in `L¹`
to `X_σ`. -/
theorem dyadic_stoppedValue_tendsto_of_bounded_stopping_times
    (hX : Supermartingale X ℱ μ) (hX_rc : HasRightContinuousPaths X)
    {σ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (hσ_bdd : ∃ T : NNReal, ∀ ω, σ ω ≤ T) :
    (∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ X (dyadicCeilApprox n σ ω) ω) atTop (𝓝 (X (σ ω) ω))) ∧
      Tendsto
        (fun n ↦ eLpNorm (fun ω ↦ X (dyadicCeilApprox n σ ω) ω - X (σ ω) ω) 1 μ)
        atTop (𝓝 0) := sorry

-- Proof sketch: approximate `σ` and `τ` from above by their dyadic ceilings, apply the
-- discrete-time optional sampling theorem to the dyadic skeleton, and then pass to the limit using
-- the convergence statements from the preceding two parts.
/-- Exercise 21.1.3 (3): a right-continuous supermartingale satisfies the optional sampling
inequality for bounded stopping times `σ ≤ τ`. -/
theorem supermartingale_condExp_stoppedValue_ae_le_of_le_of_bounded_rightContinuous
    (hX : Supermartingale X ℱ μ) (hX_rc : HasRightContinuousPaths X)
    {σ τ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
    (hστ : σ ≤ τ) (hτ_bdd : ∃ T : NNReal, ∀ ω, τ ω ≤ T) :
    μ[stoppedValue X (fun ω ↦ (τ ω : ENNReal)) | hσ.measurableSpace] ≤ᵐ[μ]
      stoppedValue X (fun ω ↦ (σ ω : ENNReal)) := sorry

-- Proof sketch: the forward implication is the martingale case of optional sampling. For the
-- converse, test the expectation identity on bounded stopping times obtained from deterministic
-- times and events in `𝓕_s`, and recover the martingale conditional-expectation identity at
-- deterministic times.
/-- Exercise 21.1.3 (4): an adapted integrable process is a martingale if and only if every
bounded stopping time preserves its initial expectation. -/
theorem martingale_iff_expected_stoppedValue_eq_initial_of_bounded_stopping_times
    (hY_adapted : Adapted ℱ Y) (hY_int : ∀ t : NNReal, Integrable (Y t) μ) :
    Martingale Y ℱ μ ↔
      ∀ τ : Ω → NNReal, IsStoppingTime ℱ (fun ω ↦ (τ ω : ENNReal)) →
        (∃ T : NNReal, ∀ ω, τ ω ≤ T) →
          μ[stoppedValue Y (fun ω ↦ (τ ω : ENNReal))] = μ[Y 0] := sorry

-- Proof sketch: truncate the finite stopping times by deterministic bounds, apply the bounded
-- optional sampling inequality to the truncations, use uniform integrability and right continuity
-- to pass the stopped values to the limit in `L¹`, and retain both the integrability of
-- `X_τ` and the limiting conditional-expectation inequality.
/-- Exercise 21.1.3 (5): if `X` is uniformly integrable and `σ ≤ τ` are finite stopping times,
then `X_τ` is integrable and the optional sampling inequality still holds without boundedness. -/
theorem supermartingale_condExp_stoppedValue_ae_le_of_uniformIntegrable_of_le
    (hX : Supermartingale X ℱ μ) (hX_rc : HasRightContinuousPaths X)
    (hX_UI : UniformIntegrable X 1 μ)
    {σ τ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
    (hστ : σ ≤ τ) :
    Integrable (stoppedValue X (fun ω ↦ (τ ω : ENNReal))) μ ∧
      μ[stoppedValue X (fun ω ↦ (τ ω : ENNReal)) | hσ.measurableSpace] ≤ᵐ[μ]
        stoppedValue X (fun ω ↦ (σ ω : ENNReal)) := sorry

-- Proof sketch: for deterministic times `s ≤ t`, identify
-- `stoppedProcess X τ t = X_{τ ∧ t}` and apply the bounded optional sampling inequality from part
-- (3) to the stopping times `τ ∧ s` and `τ ∧ t`.
/-- Exercise 21.1.3 (6): for an arbitrary stopping time `τ`, the stopped process
`(X_{τ ∧ t})_{t ≥ 0}` is again a supermartingale. -/
theorem stoppedProcess_supermartingale_of_optional_stopping
    (hX : Supermartingale X ℱ μ) (hX_rc : HasRightContinuousPaths X)
    {τ : Ω → ENNReal} (hτ : IsStoppingTime ℱ τ) :
    Supermartingale (stoppedProcess X τ) ℱ μ := sorry
end ProbabilityTheory

/-! ### Exercise_21_1_4 (from Items/Chap21) -/
open MeasureTheory
open scoped MeasureTheory Topology NNReal ENNReal

noncomputable section

universe u v

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]
variable {X : ℝ≥0 → Ω → E}

/-- Exercise 21.1.4 (1): if each time slice `X t` is measurable and every sample path is right
continuous on `[0, ∞)`, then the process is jointly measurable as a map on time and sample space.
-/
-- Proof sketch: approximate each path on `[0, ∞)` by right-step processes built from rational or
-- dyadic times. Each approximant is jointly measurable because it is piecewise constant in time
-- with measurable coefficients `X q`, and the right-continuity of the paths identifies `X` as the
-- pointwise limit of these approximants.
theorem measurable_uncurry_of_measurable_rightContinuous
    (hX_meas : ∀ t, Measurable (X t))
    (hX_right_cont : ∀ (ω : Ω) (t : ℝ≥0),
      ContinuousWithinAt (fun s : ℝ≥0 ↦ X s ω) (Set.Ici t) t) :
    Measurable (Function.uncurry X) := sorry

namespace Adapted

/-- Exercise 21.1.4 (2): an adapted right-continuous process on a Polish state space is
progressively measurable. -/
-- Proof sketch: for each deterministic horizon `t`, restrict the process to `[0, t]`. Adaptedness
-- makes every time section measurable with respect to `ℱ t`, and right-continuity lets one again
-- approximate the restriction by step processes using only times in `[0, t]`, yielding the
-- required measurability on `Set.Iic t × Ω`.
theorem progMeasurable_of_rightContinuous
    {ℱ : Filtration ℝ≥0 inferInstance}
    {X : ℝ≥0 → Ω → E}
    (hX_adapted : Adapted ℱ X)
    (hX_right_cont : ∀ (ω : Ω) (t : ℝ≥0),
      ContinuousWithinAt (fun s : ℝ≥0 ↦ X s ω) (Set.Ici t) t) :
    ProgMeasurable ℱ X := sorry

end Adapted

/-- Exercise 21.1.4 (3): evaluating an adapted right-continuous process at a finite stopping time
is measurable with respect to the stopping-time σ-algebra. -/
-- Proof sketch: part (2) gives progressive measurability. Identify `ω ↦ X (τ ω) ω` with the
-- stopped value of `X` at the finite stopping time `τ`, and then apply the standard theorem that
-- the stopped value of a progressively measurable process is measurable for `𝓕_τ`.
theorem measurable_stoppedValue_of_adapted_rightContinuous
    {ℱ : Filtration ℝ≥0 inferInstance} {τ : Ω → ℝ≥0}
    (hX_adapted : Adapted ℱ X)
    (hX_right_cont : ∀ (ω : Ω) (t : ℝ≥0),
      ContinuousWithinAt (fun s : ℝ≥0 ↦ X s ω) (Set.Ici t) t)
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop ℝ≥0)) :
    Measurable[hτ.measurableSpace] (fun ω ↦ X (τ ω) ω) := by
  simpa [stoppedValue] using
    measurable_stoppedValue (hX_adapted.progMeasurable_of_rightContinuous hX_right_cont) hτ

end MeasureTheory
