import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_21_51 (from Items/Chap21) -/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u v

local notation "PathSpace" => C(NNReal, ℝ)

/-- The continuous path space `C([0, ∞), ℝ)` is equipped with its Borel `σ`-algebra in this
item. -/
local instance pathSpaceMeasurableSpace : MeasurableSpace PathSpace := borel _

/-- The path space `C([0, ∞), ℝ)` is a Borel space for its compact-open topology. -/
local instance pathSpaceBorelSpace : BorelSpace PathSpace := ⟨rfl⟩

-- Proof sketch: evaluation at each fixed time is continuous on `C([0, ∞), ℝ)`, hence the
-- resulting finite tuple of evaluations is measurable.
/-- The coordinate projection sending a continuous path to its values at a finite tuple of times is
measurable. -/
theorem measurable_continuousPathProjection {m : ℕ} (times : Fin (m + 1) → NNReal) :
    Measurable (fun ω : PathSpace ↦ fun i ↦ ω (times i)) := sorry

/-- The finite-dimensional marginal of a probability law on `C([0, ∞), ℝ)` along the tuple of
times `times`. -/
noncomputable def continuousPathFiniteDimensionalDistribution (μ : ProbabilityMeasure PathSpace)
    {m : ℕ} (times : Fin (m + 1) → NNReal) : ProbabilityMeasure (Fin (m + 1) → ℝ) :=
  μ.map (measurable_continuousPathProjection times).aemeasurable

-- Proof sketch: unfold `continuousPathFiniteDimensionalDistribution`; it is the pushforward of
-- `μ` by the coordinate projection `ω ↦ (ω (times i))ᵢ`.
/-- Coercing a finite-dimensional marginal to a measure gives the corresponding pushforward
measure. -/
theorem continuousPathFiniteDimensionalDistribution_toMeasure
    (μ : ProbabilityMeasure PathSpace) {m : ℕ} (times : Fin (m + 1) → NNReal) :
    (continuousPathFiniteDimensionalDistribution μ times : Measure (Fin (m + 1) → ℝ)) =
      Measure.map (fun ω : PathSpace ↦ fun i ↦ ω (times i)) (μ : Measure PathSpace) := sorry

/-- The probability law of a `C([0, ∞), ℝ)`-valued random variable. -/
noncomputable def continuousPathLaw {Ω : Type u} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → PathSpace) (hX : Measurable X) :
    ProbabilityMeasure PathSpace :=
  P.map hX.aemeasurable

-- Proof sketch: unfold `continuousPathLaw`; it is the pushforward of `P` by the measurable
-- path-valued map `X`.
/-- Coercing `continuousPathLaw P X hX` to a measure gives the pushforward of `P` by `X`. -/
theorem continuousPathLaw_toMeasure {Ω : Type u} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → PathSpace) (hX : Measurable X) :
    (continuousPathLaw P X hX : Measure PathSpace) = Measure.map X (P : Measure Ω) := sorry

/-- The piecewise linearly interpolated population path obtained from the discrete Galton--Watson
process `Z`, with time speed-up by `n` and space scaling by `1 / n`. This is the textbook
rescaled process `\bar Z^n`. -/
def rescaledGaltonWatsonPathFun {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) : NNReal → ℝ :=
  if _h : n = 0 then
    fun _ ↦ (Z 0 ω : ℝ)
  else
    fun t ↦
      let x : ℝ := (n : ℝ) * (t : ℝ)
      let k : ℕ := Nat.floor x
      (((k + 1 : ℝ) - x) * (Z k ω : ℝ) + (x - k) * (Z (k + 1) ω : ℝ)) / n

-- Proof sketch: unfold `rescaledGaltonWatsonPathFun`; this is the defining interpolation formula,
-- with the harmless constant-path convention at `n = 0`.
/-- Expanding `rescaledGaltonWatsonPathFun` recovers the textbook linear interpolation formula for
the rescaled branching process. -/
theorem rescaledGaltonWatsonPathFun_apply {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) (t : NNReal) :
    rescaledGaltonWatsonPathFun Z n ω t =
      if h : n = 0 then
        (Z 0 ω : ℝ)
      else
        let x : ℝ := (n : ℝ) * (t : ℝ)
        let k : ℕ := Nat.floor x
        (((k + 1 : ℝ) - x) * (Z k ω : ℝ) + (x - k) * (Z (k + 1) ω : ℝ)) / n := sorry

-- Proof sketch: for `n = 0` the path is constant. For `n > 0`, on each interval
-- `[k / n, (k + 1) / n]` the displayed formula is affine in `t`, and neighboring affine pieces
-- agree at the mesh points because both evaluate to `Z k / n`.
/-- For each sample point `ω`, the rescaled interpolation formula defines a continuous path on
`[0, ∞)`. -/
theorem continuous_rescaledGaltonWatsonPathFun {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) :
    Continuous (rescaledGaltonWatsonPathFun Z n ω) := sorry

/-- The path-valued version of the textbook rescaled Galton--Watson process `\bar Z^n`. -/
def rescaledGaltonWatsonPath {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℕ → Ω → ℕ) (n : ℕ) : Ω → PathSpace :=
  fun ω ↦
    ⟨rescaledGaltonWatsonPathFun Z n ω, continuous_rescaledGaltonWatsonPathFun Z n ω⟩

-- Proof sketch: `rescaledGaltonWatsonPath` is obtained by packaging the scalar interpolation
-- `rescaledGaltonWatsonPathFun Z n ω` together with its continuity theorem.
/-- Evaluating the path-valued rescaled process at time `t` gives the scalar interpolation
formula. -/
theorem rescaledGaltonWatsonPath_apply {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) (t : NNReal) :
    rescaledGaltonWatsonPath Z n ω t = rescaledGaltonWatsonPathFun Z n ω t := sorry

-- Proof sketch: coordinate evaluation on `PathSpace` is measurable, and every coordinate
-- `ω ↦ Z k ω` is measurable by hypothesis; then Theorem 21.31 identifies the path-space Borel
-- `σ`-algebra with the coordinate-generated one.
/-- The rescaled Galton--Watson path is a measurable `C([0, ∞), ℝ)`-valued random variable when
all discrete population coordinates are measurable. -/
theorem measurable_rescaledGaltonWatsonPath {Ω : Type u} [MeasurableSpace Ω]
    {Z : ℕ → Ω → ℕ} (hZ_meas : ∀ k : ℕ, Measurable (Z k)) (n : ℕ) :
    Measurable (rescaledGaltonWatsonPath Z n) := sorry

/-- The probability law of the rescaled Galton--Watson path `\bar Z^n`. -/
noncomputable def rescaledGaltonWatsonPathLaw {Ω : Type u} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) (hZ_meas : ∀ k : ℕ, Measurable (Z k))
    (n : ℕ) : ProbabilityMeasure PathSpace :=
  continuousPathLaw P (rescaledGaltonWatsonPath Z n) (measurable_rescaledGaltonWatsonPath hZ_meas n)

-- Proof sketch: unfold `rescaledGaltonWatsonPathLaw`; it is the pushforward of `P` by the
-- path-valued map `rescaledGaltonWatsonPath Z n`.
/-- Coercing the rescaled Galton--Watson path law to a measure gives the corresponding
pushforward measure on `C([0, ∞), ℝ)`. -/
theorem rescaledGaltonWatsonPathLaw_toMeasure {Ω : Type u} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) (hZ_meas : ∀ k : ℕ, Measurable (Z k))
    (n : ℕ) :
    (rescaledGaltonWatsonPathLaw P Z hZ_meas n : Measure PathSpace) =
      Measure.map (rescaledGaltonWatsonPath Z n) (P : Measure Ω) := sorry

/-- A path-valued random variable `Y` has the one-dimensional marginals of Feller's branching
diffusion started from `x` if it starts at `x` almost surely and satisfies the textbook Laplace
transform formula at every time. -/
def HasFellerBranchingDiffusionPathLaw {Ω : Type u} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (Y : Ω → PathSpace) (x : NNReal) : Prop :=
  (P : Measure Ω) {ω | Y ω 0 = (x : ℝ)} = 1 ∧
    ∀ t l : NNReal,
      ∫ ω, Real.exp (-((l : ℝ) * Y ω t)) ∂(P : Measure Ω) =
        Real.exp (-((l : ℝ) * (x : ℝ)) / (((l : ℝ) * (t : ℝ)) + 1))

-- Proof sketch: this is the defining pair of conditions, namely the a.s. initial-value identity
-- and the explicit Laplace-transform formula for every time marginal.
/-- Unfolding `HasFellerBranchingDiffusionPathLaw` gives the initial-value and Laplace-transform
characterization of the Feller branching-diffusion path law. -/
theorem hasFellerBranchingDiffusionPathLaw_iff {Ω : Type u} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (Y : Ω → PathSpace) (x : NNReal) :
    HasFellerBranchingDiffusionPathLaw P Y x ↔
      (P : Measure Ω) {ω | Y ω 0 = (x : ℝ)} = 1 ∧
        ∀ t l : NNReal,
          ∫ ω, Real.exp (-((l : ℝ) * Y ω t)) ∂(P : Measure Ω) =
            Real.exp (-((l : ℝ) * (x : ℝ)) / (((l : ℝ) * (t : ℝ)) + 1)) := sorry

-- Proof sketch: identify the rescaled branching laws with their path-space pushforwards, use the
-- assumed finite-dimensional convergence of the coordinate processes, combine it with the
-- assumed tightness of the path laws, and invoke Theorem 21.38 to conclude weak convergence on
-- `C([0, ∞), ℝ)`.
/-- Theorem 21.51: if the rescaled Galton--Watson paths `\bar Z^n` have finite-dimensional
distributions converging to those of a path-valued Feller branching diffusion `Y` started from
`x`, and if the path laws of `\bar Z^n` are tight in `C([0, ∞), ℝ)`, then the laws
`𝓛_x[\bar Z^n]` converge weakly to `𝓛_x[Y]`. -/
theorem rescaledGaltonWatsonPathLaw_tendsto_fellerBranchingDiffusion
    {Ω : ℕ → Type u} [∀ n : ℕ, MeasurableSpace (Ω n)]
    {Ω' : Type v} [MeasurableSpace Ω']
    (x : NNReal)
    (PZ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (Z : (n : ℕ) → ℕ → Ω n → ℕ)
    (hZ_meas : ∀ n k : ℕ, Measurable (Z n k))
    (PY : ProbabilityMeasure Ω')
    (Y : Ω' → PathSpace)
    (hY_meas : Measurable Y)
    (hY : HasFellerBranchingDiffusionPathLaw PY Y x)
    (hfdd :
      ∀ m : ℕ, ∀ times : Fin (m + 1) → NNReal,
        Tendsto
          (fun n ↦
            continuousPathFiniteDimensionalDistribution
              (rescaledGaltonWatsonPathLaw (PZ n) (Z n) (hZ_meas n) n) times)
          atTop
          (𝓝
            (continuousPathFiniteDimensionalDistribution
              (continuousPathLaw PY Y hY_meas) times)))
    (htight :
      IsTightMeasureSet
        (Set.range fun n ↦
          (rescaledGaltonWatsonPathLaw (PZ n) (Z n) (hZ_meas n) n : Measure PathSpace))) :
    Tendsto
      (fun n ↦ rescaledGaltonWatsonPathLaw (PZ n) (Z n) (hZ_meas n) n)
      atTop
      (𝓝 (continuousPathLaw PY Y hY_meas)) := sorry
