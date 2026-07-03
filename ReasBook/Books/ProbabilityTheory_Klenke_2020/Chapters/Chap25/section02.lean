import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_25_2_1 (from Items/Chap25) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

local notation "PathSpace" => C(NNReal, ℝ)
local notation "Process" => NNReal → Ω → ℝ

variable [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal mΩ}
variable {M H N : Process}

-- Proof sketch: compare the partition sums with elementary predictable approximants of the
-- continuous integrand `H`, use the Itô isometry for the stopped approximants and the continuity
-- of `H` to control the discretization error, and identify the limit with the chosen Itô integral
-- process `N`.
/-- Exercise 25.2.1 (1): part (i). For every horizon `T`, if `N` is an Itô integral process for
`H` against the continuous local martingale `M`, then the partition sums along any admissible
sequence converge in probability to `N T`. -/
theorem tendstoInMeasure_partitionItoApproximationUpTo
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (hN : IsContinuousLocalMartingaleItoIntegral hbr H N)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) :
    TendstoInMeasure μ
      (fun n ω ↦
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ H t ω)
          (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
          P
          T
          n)
      atTop
      (N T) := sorry

-- Proof sketch: first obtain convergence in probability at each rational horizon from part (i),
-- then extract a diagonal subsequence. Use continuity of the sample paths of `H`, `M`, and `N`
-- together with the monotonic refinement of the admissible partitions to upgrade the rational-time
-- almost-sure convergence to simultaneous convergence for all `T ≥ 0`.
/-- Exercise 25.2.1 (2): part (ii). There is a subsequence of the admissible partition rows along
which the partition sums converge almost surely to the Itô integral process `N` simultaneously for
every time horizon `T`. -/
theorem exists_partitionSubsequence_with_ae_pathwise_itoApproximation
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ H t ω)
    (hN : IsContinuousLocalMartingaleItoIntegral hbr H N)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        ∀ᵐ ω ∂μ, ∀ T : NNReal,
          Tendsto
            (fun n ↦
              partitionPathwiseItoApproximationUpTo
                (fun t ↦ H t ω)
                (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
                P
                T
                (φ n))
            atTop
            (𝓝 (N T ω)) := sorry

end ProbabilityTheory

/-! ### Definition_25_2 (from Items/Chap25) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "ContinuousFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

/-- A finite predictable-step representation of a real-valued process on `Ω × [0, ∞)`. -/
structure PredictableStepRepresentation (ℱ : ContinuousFiltration) where
  /-- The number of stochastic time intervals. -/
  n : ℕ
  /-- The time partition `0 = t₀ < t₁ < ⋯ < tₙ` indexed by `Fin (n + 1)`. -/
  times : Fin (n + 1) → NNReal
  /-- The coefficient functions `h₀, …, hₙ₋₁` used on the successive time intervals. -/
  coeff : Fin n → Ω → ℝ
  /-- The partition starts at time `0`. -/
  times_zero : times 0 = 0
  /-- The partition times are strictly increasing. -/
  times_strictMono : StrictMono times
  /-- Each coefficient is bounded. -/
  coeff_bounded : ∀ i, ∃ C : ℝ, ∀ ω, |coeff i ω| ≤ C
  /-- Each coefficient is measurable with respect to the previous filtration time. -/
  coeff_measurable : ∀ i, Measurable[ℱ (times i.castSucc)] (coeff i)

/-- The piecewise-constant process associated to a predictable-step representation. -/
noncomputable def PredictableStepRepresentation.toProcess {ℱ : ContinuousFiltration}
    (data : PredictableStepRepresentation ℱ) : Process :=
  fun t ω ↦
    ∑ i,
      data.coeff i ω *
        Set.indicator (Set.Ioc (data.times i.castSucc) (data.times i.succ))
          (fun _ : NNReal ↦ (1 : ℝ)) t

-- Proof sketch: unfold `PredictableStepRepresentation.toProcess`; the process is defined by this
-- finite sum of coefficient functions times interval indicators.
/-- The process attached to a predictable-step datum is exactly the advertised finite sum over the
partition intervals. -/
theorem PredictableStepRepresentation.toProcess_apply {ℱ : ContinuousFiltration}
    (data : PredictableStepRepresentation ℱ) (t : NNReal) (ω : Ω) :
    data.toProcess t ω =
      ∑ i,
        data.coeff i ω *
          Set.indicator (Set.Ioc (data.times i.castSucc) (data.times i.succ))
            (fun _ : NNReal ↦ (1 : ℝ)) t :=
  rfl

private def zeroPredictableStepRepresentation (ℱ : ContinuousFiltration) :
    PredictableStepRepresentation ℱ where
  n := 0
  times := fun _ ↦ 0
  coeff := fun i ↦ Fin.elim0 i
  times_zero := rfl
  times_strictMono := by
    intro i j hij
    fin_cases i
    fin_cases j
    cases hij
  coeff_bounded := by
    intro i
    exact Fin.elim0 i
  coeff_measurable := by
    intro i
    exact Fin.elim0 i

private theorem zeroPredictableStepRepresentation_toProcess (ℱ : ContinuousFiltration) :
    (zeroPredictableStepRepresentation ℱ).toProcess = 0 := by
  funext t ω
  simp [zeroPredictableStepRepresentation, PredictableStepRepresentation.toProcess]

private def smulPredictableStepRepresentation {ℱ : ContinuousFiltration} (a : ℝ)
    (data : PredictableStepRepresentation ℱ) : PredictableStepRepresentation ℱ where
  n := data.n
  times := data.times
  coeff := fun i ω ↦ a * data.coeff i ω
  times_zero := data.times_zero
  times_strictMono := data.times_strictMono
  coeff_bounded := by
    intro i
    rcases data.coeff_bounded i with ⟨C, hC⟩
    refine ⟨|a| * C, ?_⟩
    intro ω
    calc
      |a * data.coeff i ω| = |a| * |data.coeff i ω| := by simp [abs_mul]
      _ ≤ |a| * C := mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg a)
  coeff_measurable := by
    intro i
    exact Measurable.const_mul (data.coeff_measurable i) a

private theorem smulPredictableStepRepresentation_toProcess {ℱ : ContinuousFiltration} (a : ℝ)
    (data : PredictableStepRepresentation ℱ) :
    (smulPredictableStepRepresentation a data).toProcess = a • data.toProcess := by
  funext t ω
  change
    ∑ i,
      (a * data.coeff i ω) *
        Set.indicator (Set.Ioc (data.times i.castSucc) (data.times i.succ))
          (fun _ : NNReal ↦ (1 : ℝ)) t =
      a *
        ∑ i,
          data.coeff i ω *
            Set.indicator (Set.Ioc (data.times i.castSucc) (data.times i.succ))
              (fun _ : NNReal ↦ (1 : ℝ)) t
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  ring

private theorem add_mem_predictableSimpleProcesses {ℱ : ContinuousFiltration} {H K : Process}
    (hH : ∃ representation : PredictableStepRepresentation ℱ, H = representation.toProcess)
    (hK : ∃ representation : PredictableStepRepresentation ℱ, K = representation.toProcess) :
    ∃ representation : PredictableStepRepresentation ℱ,
      H + K = representation.toProcess := by
  sorry

/-- Definition 25.2: the vector space `𝓔` of predictable simple processes is the subspace of
real-valued processes on `Ω × [0, ∞)` that admit a finite piecewise-constant representation
`H_t(ω) = ∑ i h_i(ω) 1_(tᵢ,tᵢ₊₁](t)` with bounded coefficients `h_i` that are measurable with
respect to the preceding filtration time. -/
def predictableSimpleProcesses (ℱ : ContinuousFiltration) : Submodule ℝ Process where
  carrier := {H | ∃ representation : PredictableStepRepresentation ℱ, H = representation.toProcess}
  zero_mem' := by
    refine ⟨zeroPredictableStepRepresentation ℱ, ?_⟩
    exact zeroPredictableStepRepresentation_toProcess ℱ
  add_mem' := by
    intro H K hH hK
    exact add_mem_predictableSimpleProcesses hH hK
  smul_mem' := by
    intro a H hH
    rcases hH with ⟨data, rfl⟩
    refine ⟨smulPredictableStepRepresentation a data, ?_⟩
    symm
    exact smulPredictableStepRepresentation_toProcess a data

/-- A short chapter-wide name for the canonical subtype of the textbook vector space `𝓔`. -/
abbrev PredictableSimpleProcess (ℱ : ContinuousFiltration) :=
  predictableSimpleProcesses ℱ

namespace PredictableSimpleProcess

/-- Every predictable simple process admits a finite predictable-step representation. -/
theorem exists_representation {ℱ : ContinuousFiltration} (H : PredictableSimpleProcess ℱ) :
    ∃ representation : PredictableStepRepresentation ℱ, (H : Process) = representation.toProcess :=
  H.2

end PredictableSimpleProcess

/-- Every predictable-step datum defines an element of `predictableSimpleProcesses ℱ`. -/
theorem PredictableStepRepresentation.mem_predictableSimpleProcesses {ℱ : ContinuousFiltration}
    (data : PredictableStepRepresentation ℱ) :
    data.toProcess ∈ predictableSimpleProcesses ℱ :=
  ⟨data, rfl⟩

/-- Every predictable-step datum defines a canonical predictable simple process. -/
noncomputable def PredictableStepRepresentation.toPredictableSimpleProcess
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) :
    PredictableSimpleProcess ℱ :=
  ⟨data.toProcess, data.mem_predictableSimpleProcesses⟩

/-- Coercing the canonical predictable simple process attached to a representation recovers the
underlying process. -/
@[simp] theorem PredictableStepRepresentation.toPredictableSimpleProcess_coe
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) :
    (data.toPredictableSimpleProcess : Process) = data.toProcess :=
  rfl

/-- The product measure `μ ⊗ dt` on `Ω × [0, ∞)` used for the `L²` theory of processes. -/
noncomputable abbrev processMeasure (μ : Measure Ω) : Measure (Ω × ℝ) :=
  μ.prod ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ)))

/-- Regard a nonnegative-time process as a function on `Ω × ℝ`, with negative times clamped to
`0`. On `processMeasure μ`, this agrees almost everywhere with the usual restriction to
`Ω × [0, ∞)`. -/
abbrev processToTimeSpaceFun (H : Process) : Ω × ℝ → ℝ :=
  Function.uncurry fun ω (t : ℝ) ↦ H t.toNNReal ω

/-- The canonical `L²(μ ⊗ dt)` image of the globally square-integrable predictable simple
processes from Definition 25.2. -/
def predictableSimpleProcessL2 (ℱ : ContinuousFiltration) (μ : Measure Ω) :
    Submodule ℝ (Lp ℝ 2 (processMeasure μ)) where
  carrier := {f | ∃ H : PredictableSimpleProcess ℱ,
    ∃ hH : MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ),
      f = hH.toLp (processToTimeSpaceFun (H : Process))}
  zero_mem' := by
    have h0 : MemLp (processToTimeSpaceFun ((0 : PredictableSimpleProcess ℱ) : Process))
        (2 : ℝ≥0∞) (processMeasure μ) := by
      change MemLp (0 : Ω × ℝ → ℝ) (2 : ℝ≥0∞) (processMeasure μ)
      exact (MemLp.zero : MemLp (0 : Ω × ℝ → ℝ) (2 : ℝ≥0∞) (processMeasure μ))
    refine ⟨0, h0, ?_⟩
    change h0.toLp (0 : Ω × ℝ → ℝ) = 0
    exact MemLp.toLp_zero h0
  add_mem' := by
    intro f g hf hg
    rcases hf with ⟨H, hH, rfl⟩
    rcases hg with ⟨G, hG, rfl⟩
    refine ⟨H + G, by
      simpa [processToTimeSpaceFun] using hH.add hG, ?_⟩
    simpa [processToTimeSpaceFun] using MemLp.toLp_add hH hG
  smul_mem' := by
    intro a f hf
    rcases hf with ⟨H, hH, rfl⟩
    refine ⟨a • H, by
      simpa [processToTimeSpaceFun] using hH.const_smul a, ?_⟩
    simpa [processToTimeSpaceFun] using MemLp.toLp_const_smul a hH

/-- A globally square-integrable predictable simple process defines an element of the canonical
`L²(μ ⊗ dt)` space of predictable simple integrands. -/
theorem toLp_mem_predictableSimpleProcessL2
    {ℱ : ContinuousFiltration} {μ : Measure Ω} (H : PredictableSimpleProcess ℱ)
    (hH : MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ)) :
    hH.toLp (processToTimeSpaceFun (H : Process)) ∈ predictableSimpleProcessL2 ℱ μ :=
  ⟨H, hH, rfl⟩

/-- The canonical `L²(μ ⊗ dt)` element represented by a globally square-integrable predictable
simple process. -/
noncomputable def predictableSimpleProcessToL2
    {ℱ : ContinuousFiltration} {μ : Measure Ω} (H : PredictableSimpleProcess ℱ)
    (hH : MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ)) :
    predictableSimpleProcessL2 ℱ μ :=
  ⟨hH.toLp (processToTimeSpaceFun (H : Process)),
    toLp_mem_predictableSimpleProcessL2 H hH⟩

/-- Coercing `predictableSimpleProcessToL2 H hH` to the ambient `L²(μ ⊗ dt)` space recovers the
represented `Lp` class. -/
@[simp] theorem predictableSimpleProcessToL2_coe
    {ℱ : ContinuousFiltration} {μ : Measure Ω} (H : PredictableSimpleProcess ℱ)
    (hH : MemLp (processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞) (processMeasure μ)) :
    ((predictableSimpleProcessToL2 H hH : predictableSimpleProcessL2 ℱ μ) :
      Lp ℝ 2 (processMeasure μ)) =
      hH.toLp (processToTimeSpaceFun (H : Process)) :=
  rfl

/-- The pseudonorm from Definition 25.2 on the vector space of predictable simple processes. -/
noncomputable def predictableSimpleProcessNorm {ℱ : ContinuousFiltration} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H : PredictableSimpleProcess ℱ) : ℝ :=
  Real.sqrt
    (∫ ω, ∫ t in Set.Ici (0 : ℝ), ((H : Process) t.toNNReal ω) ^ 2
      ∂ (MeasureSpace.volume : Measure ℝ) ∂ μ)

/-- The square of the pseudonorm from Definition 25.2, written directly in the integral form
`E[∫₀^∞ H_s^2 ds]`. -/
noncomputable def predictableSimpleProcessNormSq {ℱ : ContinuousFiltration} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H : PredictableSimpleProcess ℱ) : ℝ :=
  ∫ ω, ∫ t in Set.Ici (0 : ℝ), ((H : Process) t.toNNReal ω) ^ 2
    ∂ (MeasureSpace.volume : Measure ℝ) ∂ μ

/-- Unfolding `predictableSimpleProcessNormSq` gives the defining integral formula on the
underlying process. -/
theorem predictableSimpleProcessNormSq_def {ℱ : ContinuousFiltration} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H : PredictableSimpleProcess ℱ) :
    predictableSimpleProcessNormSq μ H =
      ∫ ω, ∫ t in Set.Ici (0 : ℝ), ((H : Process) t.toNNReal ω) ^ 2
        ∂ (MeasureSpace.volume : Measure ℝ) ∂ μ :=
  rfl

-- Proof sketch: a predictable-step representation is measurable with respect to the predictable
-- σ-algebra because each rectangle `(t_i, t_{i+1}] × A` with `A ∈ ℱ t_i` is predictable, and
-- finite linear combinations preserve predictability.
/-- Every element of `predictableSimpleProcesses ℱ` is predictable in mathlib's canonical
sense. -/
theorem isPredictable_of_mem_predictableSimpleProcesses {ℱ : ContinuousFiltration} {H : Process}
    (hH : H ∈ predictableSimpleProcesses ℱ) :
    IsPredictable ℱ H := sorry

/-- Every predictable simple process is predictable in mathlib's canonical sense. -/
theorem PredictableSimpleProcess.isPredictable {ℱ : ContinuousFiltration}
    (H : PredictableSimpleProcess ℱ) :
    IsPredictable ℱ (H : Process) :=
  isPredictable_of_mem_predictableSimpleProcesses H.2

-- Proof sketch: integrate the square of the step representation interval by interval. The
-- indicator functions have disjoint supports and contribute exactly the interval lengths
-- `tᵢ₊₁ - tᵢ`, yielding the textbook sum formula.
/-- For a chosen predictable-step representation, the square of the Definition 25.2 pseudonorm of
the associated predictable simple process agrees with the textbook sum
`∑ E[h_i^2] (t_{i+1} - t_i)`. -/
theorem predictableSimpleProcessNormSq_eq_sum {ℱ : ContinuousFiltration} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (data : PredictableStepRepresentation ℱ) :
    predictableSimpleProcessNormSq μ data.toPredictableSimpleProcess =
      ∑ i,
        (∫ ω, (data.coeff i ω) ^ 2 ∂ μ) *
          ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) := sorry

end MeasureTheory
