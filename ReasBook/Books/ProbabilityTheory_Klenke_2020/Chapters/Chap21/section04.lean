import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_21_4_1 (from Items/Chap21) -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

/-- The running supremum `|X|*_T` of a real-valued continuous-time process on the interval
`[0, T]`, represented canonically as an `ℝ≥0∞`-valued interval supremum. -/
def continuousRunningAbsSup (X : NNReal → Ω → ℝ) (T : NNReal) : Ω → ℝ≥0∞ :=
  fun ω ↦ ⨆ t : Set.Icc (0 : NNReal) T, ENNReal.ofReal |X t ω|

syntax:max "|" term "|*_" term : term

macro_rules
  | `(|$X|*_$T) => `(continuousRunningAbsSup $X $T)

-- Proof sketch: unfold `|X|*_T`; the statement is exactly its defining equation.
/-- Unfolding formula for the running supremum `|X|*_T`. -/
theorem continuousRunningAbsSup_apply (X : NNReal → Ω → ℝ) (T : NNReal) (ω : Ω) :
    (|X|*_T) ω =
      ⨆ t : Set.Icc (0 : NNReal) T, ENNReal.ofReal |X t ω| :=
  rfl

section DoobLp

variable [mΩ : MeasurableSpace Ω]

variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration NNReal mΩ}
variable {X : NNReal → Ω → ℝ}

-- Proof sketch: stop the process at the first time its absolute value reaches `threshold`, reduce
-- to bounded stopping times, and apply optional sampling to the nonnegative submartingale
-- `t ↦ |X t|^p`; right continuity identifies the stopped event with the hitting event of the
-- running supremum.
/-- Exercise 21.4.1 (1): on a finite measure space, for a martingale or nonnegative submartingale
with right-continuous paths, Doob's `L^p` tail estimate controls the event `{|X|*_T ≥ λ}` by the
terminal `p`-th moment. -/
theorem doobLp_tail_bound_rightContinuous
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X)
    (hX_rc : HasRightContinuousPaths X)
    {p threshold : ℝ} (hp : 1 ≤ p) (hthreshold : 0 < threshold) (T : NNReal) :
    ENNReal.ofReal (Real.rpow threshold p) *
        μ {ω | ENNReal.ofReal threshold ≤ (|X|*_T) ω} ≤
      ∫⁻ ω, ENNReal.ofReal (Real.rpow |X T ω| p) ∂μ := sorry

end DoobLp

section RunningSupMoment

variable [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω}

-- Proof sketch: for every sample point `ω`, the terminal value `|X T ω|` is one of the values
-- whose supremum defines `|X|*_T ω`, so monotonicity of `x ↦ x^p` on `ℝ≥0∞` for `p ≥ 0` gives
-- `|X T ω|^p ≤ (|X|*_T ω)^p`; integrate this pointwise inequality.
/-- Exercise 21.4.1 (2): for every nonnegative exponent `p`, the terminal `p`-th moment is bounded
by the `p`-th moment of `|X|*_T`. This is the left inequality in clause `(ii)`, stated with the
minimal exponent range used by its pointwise proof. -/
theorem terminalMoment_le_continuousRunningAbsSupMoment
    {p : ℝ} (hp : 0 ≤ p) (X : NNReal → Ω → ℝ) (T : NNReal) :
    ∫⁻ ω, ENNReal.ofReal (Real.rpow |X T ω| p) ∂μ ≤
      ∫⁻ ω, ((|X|*_T) ω) ^ p ∂μ := sorry

end RunningSupMoment

section DoobLp

variable [mΩ : MeasurableSpace Ω]

variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration NNReal mΩ}
variable {X : NNReal → Ω → ℝ}

-- Proof sketch: integrate the tail estimate from clause `(1)` against `p λ^(p-1)`, use the layer-
-- cake representation of the `p`-th moment of `|X|*_T`, and optimize the resulting Hölder bound to
-- obtain the classical constant `(p / (p - 1))^p`.
/-- Exercise 21.4.1 (3): on a finite measure space, for `p > 1`, the `p`-th moment of `|X|*_T` is
bounded by the classical Doob constant `(p / (p - 1))^p` times the terminal `p`-th moment. This
is the right inequality in clause `(ii)`. -/
theorem continuousRunningAbsSupMoment_le_doobConstant_mul_terminalMoment
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X)
    (hX_rc : HasRightContinuousPaths X)
    {p : ℝ} (hp : 1 < p) (T : NNReal) :
    ∫⁻ ω, ((|X|*_T) ω) ^ p ∂μ ≤
      ENNReal.ofReal (Real.rpow (p / (p - 1)) p) *
        ∫⁻ ω, ENNReal.ofReal (Real.rpow |X T ω| p) ∂μ := sorry

end DoobLp

-- Proof sketch: choose a filtered probability space carrying a martingale or a nonnegative
-- submartingale with a jump visible only at a non-right-continuous exceptional time; the terminal
-- `p`-th moment stays too small compared with the probability of a large earlier excursion, so the
-- tail bound from clause `(1)` fails.
/-- Exercise 21.4.1 (4): right continuity is essential. There exists a martingale or a nonnegative
submartingale without right-continuous paths for which the tail estimate in clause `(i)` fails. -/
theorem exists_process_without_rightContinuous_paths_failing_doobLp_tail_bound :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (μ : Measure Ω') (ℱ : Filtration NNReal mΩ')
      (X : NNReal → Ω' → ℝ) (T : NNReal) (p threshold : ℝ),
      IsProbabilityMeasure μ ∧
        (Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X) ∧
        ¬ HasRightContinuousPaths X ∧
        1 ≤ p ∧
        0 < threshold ∧
        ∫⁻ ω, ENNReal.ofReal (Real.rpow |X T ω| p) ∂μ <
          ENNReal.ofReal (Real.rpow threshold p) *
            μ {ω | ENNReal.ofReal threshold ≤ (|X|*_T) ω} := sorry

end ProbabilityTheory

/-! ### Exercise_21_4_2 (from Items/Chap21) -/
open Filter MeasureTheory Set
open MeasureTheory.Filtration
open scoped ENNReal Topology

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
variable {X : NNReal → Ω → ℝ}

/- Exercise 21.4.2 is `source-facing`: it concerns continuous-time martingale convergence on
`[0, ∞)` to the canonical limit process `ℱ.limitProcess X μ`.

Domain-style sampling for the owner abstraction:
* `HasRightContinuousPaths X` in Definition 21.21 is the local `core/canonical` owner for the path
  regularity input; the stronger càdlàg condition is only a derived specialization.
* `stronglyMeasurable_limitProcess` is the owner theorem for terminal measurability of
  `ℱ.limitProcess X μ`, and it already works for `NNReal`-indexed filtrations.
* The discrete chapter owners `Submartingale.memLp_limitProcess`,
  `Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable`, and
  `Submartingale.tendsto_eLpNorm_one_limitProcess` determine the correct statement shape, but they
  live over `ℕ`-indexed filtrations, so they guide the bridge design here rather than replacing the
  present theorems by exact recalls.

Primitive data versus derived API:
* primitive inputs: right continuity, submartingale or martingale structure, and the textbook
  boundedness / uniform-integrability / `L^p` hypotheses;
* derived object: the limit random variable is the canonical owner object `ℱ.limitProcess X μ`,
  not extra public data.

Accordingly, only terminal strong measurability is a direct recall, while the almost-sure and
`eLpNorm` formulations below remain `bridge/view` companions for the continuous-time setting. -/

/- The canonical limit process is already `⨆ t, ℱ t`-strongly measurable by the general owner
declaration for `Filtration.limitProcess`. -/
recall stronglyMeasurable_limitProcess

section

variable (hX_rc : HasRightContinuousPaths X)
include hX_rc

local notation "X∞" => ℱ.limitProcess X μ

-- Proof sketch: restrict the right-continuous process to a countable dense time skeleton, apply
-- Doob's inequality from Exercise 21.4.1 together with the discrete convergence theorems of
-- Chapter 11
-- to the sampled process, and then use right continuity to upgrade convergence along the
-- skeleton to convergence as `t → ∞` in continuous time, with canonical limit `X∞`.
/-- Exercise 21.4.2, Theorem 11.4 analogue: a right-continuous submartingale on `[0,∞)` whose
positive-part expectations are bounded above has an integrable canonical limit process, and the
process converges almost surely to that limit. -/
theorem rightContinuous_submartingale_convergence_to_integrable_limitProcess_of_bdd_pos_part
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺])) :
    Integrable X∞ μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) := sorry

/-- Exercise 21.4.2, Theorem 11.4 analogue, convergence component. -/
theorem rightContinuous_submartingale_ae_tendsto_limitProcess_of_bdd_pos_part
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺])) :
    ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) := by
  exact
    (rightContinuous_submartingale_convergence_to_integrable_limitProcess_of_bdd_pos_part
      hX_rc hX hpos).2

/-- Exercise 21.4.2, Theorem 11.7 analogue for martingales: a uniformly integrable
right-continuous martingale on `[0,∞)` has an integrable canonical limit process, and the process
converges almost surely to that limit. -/
theorem rightContinuous_martingale_convergence_to_integrable_limitProcess_of_uniformIntegrable
    (hX : Martingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Integrable X∞ μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) := sorry

/-- Exercise 21.4.2, Theorem 11.7 analogue, convergence component for martingales. -/
theorem rightContinuous_martingale_ae_tendsto_limitProcess_of_uniformIntegrable
    (hX : Martingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) := by
  exact
    (rightContinuous_martingale_convergence_to_integrable_limitProcess_of_uniformIntegrable
      hX_rc hX hUI).2

/-- Exercise 21.4.2, `L¹` bridge companion: a uniformly integrable right-continuous martingale on
`[0,∞)` converges to its canonical limit process in the raw `eLpNorm` formulation of `L¹`. -/
theorem rightContinuous_martingale_tendsto_eLpNorm_one_limitProcess_of_uniformIntegrable
    (hX : Martingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Tendsto (fun t ↦ eLpNorm (X t - X∞) 1 μ) atTop (𝓝 0) := sorry

/-- Exercise 21.4.2, Theorem 11.10 analogue: an `L^p`-bounded right-continuous martingale with
`1 < p` has a canonical limit process that is terminally strongly measurable, belongs to
`L^p(μ)`, and captures the almost-sure limit. -/
theorem rightContinuous_martingale_convergence_to_memLp_limitProcess_of_lp_bounded
    {p : ℝ} (hX : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ t : NNReal, eLpNorm (X t) (ENNReal.ofReal p) μ ≤ C) :
    StronglyMeasurable[⨆ t, ℱ t] X∞ ∧
      MemLp X∞ (ENNReal.ofReal p) μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω))) := sorry

/-- Exercise 21.4.2, Theorem 11.10 analogue, `L^p` bridge companion: an `L^p`-bounded
right-continuous martingale with `1 < p` converges to its canonical limit process in the raw
`eLpNorm` formulation of `L^p`. -/
theorem rightContinuous_martingale_tendsto_eLpNorm_limitProcess_of_lp_bounded
    {p : ℝ} (hX : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ t : NNReal, eLpNorm (X t) (ENNReal.ofReal p) μ ≤ C) :
    Tendsto (fun t ↦ eLpNorm (X t - X∞) (ENNReal.ofReal p) μ) atTop (𝓝 0) := sorry

omit hX_rc

end

end ProbabilityTheory

/-! ### Exercise_21_4_3 (from Items/Chap21) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal mΩ}
variable {p : ℝ}
variable {X : ℕ → NNReal → Ω → ℝ} {Xtilde : NNReal → Ω → ℝ}

private theorem fact_one_le_ofReal_of_one_le (hp : 1 ≤ p) :
    Fact (1 ≤ ENNReal.ofReal p) :=
  ⟨by
    simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp⟩

section TimewiseLpLimit

-- Proof sketch: for each fixed `s ≤ t`, pass to the limit in the martingale identities
-- `E[Xⁿ_t | ℱ_s] = Xⁿ_s`. The owner hypothesis
-- `TendstoInLp (ENNReal.ofReal p) μ (fun n ↦ X n t) (Xtilde t)` gives the `L^p` marginals and
-- their timewise convergence, hence `L¹` convergence on the probability space for `p ≥ 1`.
-- Conditional expectation is continuous in `L¹`, so the identities pass to the limit and show
-- directly that the given limit family `X̃` is itself an `ℱ`-martingale.
/-- Exercise 21.4.3 (1): if each deterministic-time slice `X^n_t` converges in `L^p` to
`X̃_t`, then the limit family `X̃` is itself an `ℱ`-martingale. -/
theorem martingale_of_timewise_lp_limit
    (hX : ∀ n : ℕ, Martingale (X n) ℱ μ)
    (hp : 1 ≤ p)
    (hlimit :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp
        TendstoInLp (ENNReal.ofReal p) μ (fun n ↦ X n t) (Xtilde t)) :
    Martingale Xtilde ℱ μ := sorry

-- Proof sketch: part (1) first shows that the given limit family `X̃` is already a martingale.
-- For each time horizon `T`, Doob's `L^p` maximal inequality upgrades the owner timewise `L^p`
-- convergence of `Xⁿ - Xᵐ` to convergence of the path suprema on `[0,T]`, so a subsequence
-- converges uniformly almost surely on every compact interval. The limit defines a process with
-- almost surely continuous paths, is a modification of `X̃`, and still receives the same timewise
-- `TendstoInLp` limit.
/-- Exercise 21.4.3 (2): if `p > 1` and every approximating martingale has almost surely
continuous paths, then the timewise `L^p` limit admits a martingale modification with almost
surely continuous paths, and the approximants still converge to that modification in `L^p` at
each deterministic time. -/
theorem exists_continuous_martingale_modification_of_timewise_lp_limit
    (hX : ∀ n : ℕ, Martingale (X n) ℱ μ)
    (hcont : ∀ n : ℕ, HasAlmostSurelyContinuousPaths μ (X n))
    (hp : 1 < p)
    (hlimit :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp.le
        TendstoInLp (ENNReal.ofReal p) μ (fun n ↦ X n t) (Xtilde t)) :
    ∃ Xc : NNReal → Ω → ℝ,
      Martingale Xc ℱ μ ∧
        AreModifications μ Xc Xtilde ∧
        HasAlmostSurelyContinuousPaths μ Xc ∧
        (∀ t : NNReal,
          letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp.le
          TendstoInLp (ENNReal.ofReal p) μ (fun n ↦ X n t) (Xc t)) := sorry

end TimewiseLpLimit

end ProbabilityTheory

/-! ### Definition_21_4 (from Items/Chap21) -/
open MeasureTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {I : Type v} [TopologicalSpace I]
variable {E : Type w} [TopologicalSpace E]

/-- Definition 21.4: an `I`-indexed stochastic process has almost surely continuous paths if for
almost every sample point `ω`, the path `t ↦ X t ω` is continuous. -/
def HasAlmostSurelyContinuousPaths (μ : Measure Ω) (X : I → Ω → E) : Prop :=
  ∀ᵐ ω ∂μ, Continuous (processPath X ω)

/-- A process has almost surely continuous paths exactly when almost every sample path is
continuous. -/
theorem hasAlmostSurelyContinuousPaths_iff (μ : Measure Ω) (X : I → Ω → E) :
    HasAlmostSurelyContinuousPaths μ X ↔
      ∀ᵐ ω ∂μ, Continuous (processPath X ω) :=
  Iff.rfl

end ProbabilityTheory

/-! ### Exercise_21_4_4 (from Items/Chap21) -/
open Filter Set Function
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Classical MeasureTheory Topology NNReal ENNReal

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} {E : Type v}

/-- The strictly positive first hitting time `τ_[X, A]` of a set `A` by the process `X`, with
value `⊤` when the path never enters `A` after time `0`. -/
def strictHittingTime (X : NNReal → Ω → E) (A : Set E) : Ω → WithTop NNReal :=
  fun ω ↦
    if _ : ∃ t : NNReal, 0 < t ∧ X t ω ∈ A then
      ((sInf {t : NNReal | 0 < t ∧ X t ω ∈ A}) : NNReal)
    else ⊤

scoped notation:arg "τ_[" X ", " A "]" => strictHittingTime X A

-- Proof sketch: unfold `strictHittingTime`; the `if`-branch returning `⊤` is exactly the failure
-- of the existence of a strictly positive hitting time, while the converse direction rewrites the
-- negated existential as pointwise avoidance of `A` at every positive time.
/-- The strictly positive hitting time `τ_[X, A]` is infinite exactly when the path avoids `A` at
every positive time. -/
theorem strictHittingTime_eq_top_iff (X : NNReal → Ω → E) (A : Set E) (ω : Ω) :
    (τ_[X, A]) ω = ⊤ ↔ ∀ t : NNReal, 0 < t → X t ω ∉ A := by
  by_cases h : ∃ t : NNReal, 0 < t ∧ X t ω ∈ A
  · rcases h with ⟨t, ht, hA⟩
    have h' : ∃ t : NNReal, 0 < t ∧ X t ω ∈ A := ⟨t, ht, hA⟩
    constructor
    · intro hEq
      have hne : (((sInf {t : NNReal | 0 < t ∧ X t ω ∈ A}) : NNReal) : WithTop NNReal) ≠ ⊤ := by
        simpa using
          (show (((sInf {t : NNReal | 0 < t ∧ X t ω ∈ A}) : NNReal) : WithTop NNReal) ≠ ⊤ from
            WithTop.coe_ne_top)
      exact False.elim <| hne <| by simpa [strictHittingTime, h'] using hEq
    · intro hAvoid
      exact False.elim (hAvoid t ht hA)
  · constructor
    · intro _ t ht hA
      exact h ⟨t, ht, hA⟩
    · intro _
      simp [strictHittingTime, h]

section Exercise2144

variable [MeasurableSpace Ω]
variable [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]
variable {X : NNReal → Ω → E} (hXsm : ∀ t, StronglyMeasurable (X t))
variable (hXcadlag : HasCadlagPaths X)

local notation "ℱX" => Filtration.natural X hXsm

-- Proof sketch: for each deterministic time `t`, the event `{τ_[X, C] ≤ t}` can be written in
-- terms of the existence of rational times `q ≤ t` with `X q` arbitrarily close to `C`, and
-- càdlàg paths plus closedness of `C` upgrade these approximating events to an exact
-- characterization inside the natural filtration.
/-- Exercise 21.4.4 (1): for a càdlàg process on a Polish space, the strictly positive first
hitting time of a closed set is a stopping time for the natural filtration generated by the
process. -/
theorem isStoppingTime_strictHittingTime_closed_natural {C : Set E} (hC : IsClosed C) :
    IsStoppingTime ℱX (τ_[X, C]) := sorry

-- Proof sketch: a stopping time for the natural filtration remains a stopping time for the larger
-- right-continuous filtration, since every event measurable with respect to `σ(X)_t` is also
-- measurable with respect to `σ(X)_t⁺`.
/-- Exercise 21.4.4 (2): the strictly positive first hitting time of a closed set is also a
stopping time for the right-continuous augmentation `𝓕⁺` of the natural filtration. -/
theorem isStoppingTime_strictHittingTime_closed_rightCont {C : Set E} (hC : IsClosed C) :
    IsStoppingTime (Filtration.rightCont ℱX) (τ_[X, C]) := sorry

-- Proof sketch: for an open set `U`, the event `{τ_[X, U] < t}` is detected by some rational time
-- `q < t` with `X q ∈ U`, so it is measurable in the natural filtration just after time `t`; the
-- right-continuous filtration converts this into measurability of `{τ_[X, U] ≤ t}` at time `t`.
/-- Exercise 21.4.4 (3): for an open set `U`, the strictly positive first hitting time is a
stopping time for the right-continuous filtration `𝓕⁺ = σ(X)⁺`. -/
theorem isStoppingTime_strictHittingTime_open_rightCont {U : Set E} (hU : IsOpen U) :
    IsStoppingTime (Filtration.rightCont ℱX) (τ_[X, U]) := sorry

-- Proof sketch: use the two-path deterministic process on `Bool` given by `t ↦ t` and `t ↦ -t`,
-- with the open set `(0, ∞)`. The strictly positive hitting time is `0` on one path and `⊤` on
-- the other, but the time-`0` natural σ-algebra is trivial because both paths start at `0`.
/-- Exercise 21.4.4 (4): in general, even for a continuous real-valued process, the strictly
positive first hitting time of an open set need not be a stopping time for the natural filtration.
-/
theorem exists_continuous_open_hittingTime_not_isStoppingTime_natural :
    ∃ X : NNReal → Bool → ℝ, ∃ hXsm : ∀ t, StronglyMeasurable (X t),
      ∃ hXcont : ∀ ω, Continuous (fun t : NNReal ↦ X t ω),
        ∃ U : Set ℝ, IsOpen U ∧
          ¬ IsStoppingTime (Filtration.natural X hXsm) (τ_[X, U]) := sorry

end Exercise2144

end ProbabilityTheory

/-! ### Exercise_21_4_5 (from Items/Chap21) -/
open MeasureTheory
open scoped MeasureTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

namespace MeasureTheory
namespace Filtration

private noncomputable abbrev completedRightLimitMeasurableSpace
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) (t : NNReal) :
    MeasurableSpace (NullMeasurableSpace Ω μ) :=
  @NullMeasurableSpace.instMeasurableSpace Ω (ℱ₊ t) (μ.trim (ℱ₊.le t))

-- Proof sketch: if `s ≤ t`, then `ℱ₊ s ≤ ℱ₊ t`. Completing with respect to the corresponding
-- trimmed measures preserves the monotonicity of the ambient null-measurable σ-algebras.
private theorem completed_right_continuous_filtration_mono
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) :
    Monotone (completedRightLimitMeasurableSpace μ ℱ) := sorry

-- Proof sketch: a set that is null-measurable for the trimmed measure
-- `μ.trim (ℱ₊.le t)` is also null-measurable for `μ`, since the trimmed measure is
-- induced from `μ` on a smaller σ-algebra.
private theorem completed_right_continuous_filtration_le
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) (t : NNReal) :
    completedRightLimitMeasurableSpace μ ℱ t ≤
      (show MeasurableSpace (NullMeasurableSpace Ω μ) from inferInstance) := sorry

/-- The textbook filtration `ℱ^{+,*}` obtained by completing each right-limit σ-algebra
`ℱ_t^+` with respect to the trimmed measure at time `t`. -/
noncomputable def completed_right_continuous_filtration
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) :
    Filtration NNReal (show MeasurableSpace (NullMeasurableSpace Ω μ) from inferInstance) where
  seq t := completedRightLimitMeasurableSpace μ ℱ t
  mono' := completed_right_continuous_filtration_mono μ ℱ
  le' := completed_right_continuous_filtration_le μ ℱ

/-- Lean notation `ℱ^+*[μ]`, formalizing the textbook completed augmentation `ℱ^{+,*}`. -/
scoped[MeasureTheory] notation:arg ℱ "^+*[" μ "]" =>
  Filtration.completed_right_continuous_filtration μ ℱ

/- The source notation `ℱ^{+,*}` is formalized by `ℱ^+*[μ]`, the filtration
`completed_right_continuous_filtration μ ℱ`
on the completed measurable space `NullMeasurableSpace Ω μ`. -/

/- At time `t`, the filtration `ℱ^+*[μ]` is the null-measurable completion of the right-limit
`σ`-algebra `ℱ_t^+` with respect to the trimmed measure `μ.trim (ℱ₊.le t)`. -/
theorem completed_right_continuous_filtration_apply
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) (t : NNReal) :
    (ℱ^+*[μ]) t =
      @NullMeasurableSpace.instMeasurableSpace Ω (ℱ₊ t) (μ.trim (ℱ₊.le t)) := rfl

/- A set is measurable for `(ℱ^+*[μ]) t` exactly when it is null-measurable for the trimmed
measure on the right-limit `σ`-algebra `ℱ₊ t`. -/
theorem measurableSet_completed_right_continuous_filtration_iff
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) (t : NNReal) {s : Set Ω} :
    MeasurableSet[(ℱ^+*[μ]) t] s ↔
      @NullMeasurableSet Ω (ℱ₊ t) s (μ.trim (ℱ₊.le t)) := Iff.rfl

/- The completed right-continuous filtration `ℱ^+*[μ]` satisfies the chapter owner property
`UsualConditions` for the completed measure `μ.completion`. -/
-- Proof sketch: right continuity comes from the defining use of `ℱ.rightCont`, and completeness at
-- time `0` is built into the passage from `μ` to `μ.completion`.
theorem completed_right_continuous_filtration_usual_conditions
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) :
    UsualConditions (ℱ^+*[μ]) μ.completion := sorry

end Filtration

open ProbabilityTheory

-- Proof sketch: for `s ≤ t`, the martingale identity `E[B_t | ℱ_u] = B_u` holds for every
-- `u ∈ Ioi s`. Passing to the right-limit `ℱ_s⁺ = ⋂ u > s, ℱ_u` identifies the conditional
-- expectation of `B_t` with the almost sure limit of `B_u` as `u ↓ s`, and almost sure continuity
-- of Brownian paths turns that limit into `B_s`. Completing `ℱ_s⁺` with respect to `μ` does not
-- change conditional expectations after passing to `μ.completion`.
/-- Exercise 21.4.5: if a Brownian motion is a martingale for `ℱ`, then it is also a martingale
for the completed right-continuous filtration `ℱ^+*[μ]`, formalizing the textbook augmentation
`ℱ^{+,*}`. The filtration-side owner theorem is
`Filtration.completed_right_continuous_filtration_usual_conditions`; this is the Brownian-motion
corollary justified by the exercise. -/
theorem brownian_martingale_completed_right_continuous_filtration
    {μ : Measure Ω} {ℱ : Filtration NNReal mΩ} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) (hBm : Martingale B ℱ μ) :
    Martingale B (ℱ^+*[μ]) μ.completion := sorry

end MeasureTheory
