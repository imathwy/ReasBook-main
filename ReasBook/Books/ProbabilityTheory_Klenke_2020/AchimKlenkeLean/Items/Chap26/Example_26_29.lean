import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_25
import ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_10
import ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_28

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

local notation "State" => Fin 1 → ℝ

/- Domain-style sampling for Example 26.29:
- primary domain: one-dimensional weak SDE solutions together with continuous-time Markov-process
  duality and the Chapter 17 strong-Markov owner language;
- sampled owner declarations: `GeneralizedWeakSDESolution`, `SatisfiesDualityAt`,
  `localMartingaleProblemWellPosed_of_duality`,
  `canonicalPathProcess_hasStrongMarkovProperty_of_localMartingaleProblemWellPosed`,
  `HasGeneratorMatrix`, and `IsMarkovProcessRealization`;
- owner abstraction: the source-facing Wright--Fisher example is organized around the chapter's
  duality owner `SatisfiesDualityAt`, the martingale-problem owner
  `LocalMartingaleProblemWellPosed`, and the Chapter 17 owners
  `IsTimeHomogeneousMarkovProcess` / `HasStrongMarkovProperty`;
- primitive data kept here: the scalar Wright--Fisher diffusion coefficient, the polynomial
  duality function, and the pure-death Q-matrix on `ℕ`;
- derived API kept here: the dual-process existence statement, the fixed-start duality theorem,
  the moment-duality identity, the owner-level well-posedness theorem, the strong-Markov
  realization theorem, and the weak-solution corollaries.

Layer triage:
- source-facing: `wrightFisherScalarDiffusionCoeff`, `wrightFisherDualityFunction`,
  `wrightFisherDualQMatrix`, `satisfiesDualityAt_wrightFisherDual`,
  `wrightFisherMoment_eq_dualExpectation`, and the Wright--Fisher existence/uniqueness theorems;
- core/canonical: `GeneralizedWeakSDESolution`, `SatisfiesDualityAt`,
  `LocalMartingaleProblemWellPosed`, `IsTimeHomogeneousMarkovProcess`,
  `HasStrongMarkovProperty`, and `WeakSDESolution.IsWeaklyUnique`;
- bridge/view: `oneDimensionalState`, `oneDimensionalDiffusion`, `oneDimensionalDrift`, and
  `pathProcess`. -/

/-- The scalar diffusion coefficient of the Wright--Fisher SDE,
`𝟙_[0,1](x) * sqrt (γ x (1 - x))`. -/
def wrightFisherScalarDiffusionCoeff (γ : ℝ) : NNReal → ℝ → ℝ :=
  fun _ ↦ Set.indicator (Set.Icc (0 : ℝ) 1) fun y ↦ Real.sqrt (γ * y * (1 - y))

/-- The polynomial duality function `H(x, n) = x^n`, written on the chapter's one-dimensional
state space `Fin 1 → ℝ` with the canonical complex codomain of `SatisfiesDualityAt`. -/
def wrightFisherDualityFunction : State → ℕ → ℂ :=
  fun x n ↦ (x 0 : ℂ) ^ n

/-- Evaluating the Wright--Fisher duality function at the deterministic state `x` gives the usual
polynomial observable `x^n`. -/
theorem wrightFisherDualityFunction_oneDimensionalState (x : ℝ) (n : ℕ) :
    wrightFisherDualityFunction (oneDimensionalState x) n = (x : ℂ) ^ n := by
  simp [wrightFisherDualityFunction, oneDimensionalState]

/-- The pure-death Q-matrix on `ℕ` used as the Wright--Fisher moment dual. -/
def wrightFisherDualQMatrix (γ : ℝ) : ℕ → ℕ → ℝ :=
  fun m n ↦
    if n + 1 = m then γ * (Nat.choose m 2 : ℝ)
    else if n = m then -γ * (Nat.choose m 2 : ℝ)
    else 0

-- Proof sketch: each off-diagonal row has at most one nonzero entry, namely the death jump
-- `m ↦ m - 1` with rate `γ * (m choose 2)`, and the diagonal entry is the negative of that rate,
-- so every row sums to `0`.
/-- For `γ ≥ 0`, the Wright--Fisher pure-death generator is a Q-matrix on `ℕ`. -/
theorem wrightFisherDualQMatrix_isQMatrix (γ : ℝ) (hγ : 0 ≤ γ) :
    IsQMatrix (wrightFisherDualQMatrix γ) := sorry

-- Proof sketch: Example 26.29 uses the explicit pure-death chain whose generator is
-- `wrightFisherDualQMatrix γ`; this theorem packages that chain directly in the canonical Chapter
-- 17 Markov-process owner language.
/-- For `γ ≥ 0`, the Wright--Fisher dual pure-death chain exists as a continuous-time Markov
process on `ℕ` whose transition semigroup has generator matrix `wrightFisherDualQMatrix γ`. -/
theorem exists_wrightFisherDualProcess (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ κ : NNReal → Kernel ℕ ℕ,
      HasGeneratorMatrix κ (wrightFisherDualQMatrix γ) ∧
        ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (Q : ℕ → ProbabilityMeasure Ω')
          (Y : NNReal → Ω' → ℕ), IsMarkovProcessRealization κ Q Y := sorry

section WrightFisher

variable {γ x : ℝ}

local notation "σWF" => oneDimensionalDiffusion (wrightFisherScalarDiffusionCoeff γ)
local notation "bWF" => oneDimensionalDrift (fun _ _ ↦ (0 : ℝ))
local notation "WFSolution" =>
  GeneralizedWeakSDESolution
    (Measure.dirac (oneDimensionalState x))
    σWF bWF

/-- The `n`-th moment function `t ↦ E[X_t^n]` of a Wright--Fisher weak solution. -/
def wrightFisherMoment (L : WFSolution) (n : ℕ) (t : NNReal) : ℝ :=
  ∫ ω, (L ω t 0) ^ n ∂L.μ

-- Proof sketch: identify the Wright--Fisher polynomial observable with the duality function
-- `H(u, n) = u^n`, realize the pure-death chain by `exists_wrightFisherDualProcess`, and apply
-- the Itô-generator computation of Example 26.29 to verify the owner predicate
-- `SatisfiesDualityAt`.
/-- The source-facing Wright--Fisher duality of Example 26.29, expressed through the chapter's
fixed-start duality owner `SatisfiesDualityAt`. -/
theorem satisfiesDualityAt_wrightFisherDual
    (L : WFSolution) (hγ : 0 ≤ γ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hL_mem : ∀ ω : L.Ω, ∀ t : NNReal, L ω t 0 ∈ Set.Icc (0 : ℝ) 1)
    {Ω' : Type u} [MeasurableSpace Ω']
    {κ : NNReal → Kernel ℕ ℕ} {Q : ℕ → ProbabilityMeasure Ω'}
    {Y : NNReal → Ω' → ℕ}
    [IsMarkovProcessRealization κ Q Y]
    (hY_generator : HasGeneratorMatrix κ (wrightFisherDualQMatrix γ)) :
    SatisfiesDualityAt L.μ (pathProcess L.X) (oneDimensionalState x) Q (fun _ ↦ Y)
      wrightFisherDualityFunction := sorry

-- Proof sketch: this is the scalar specialization of
-- `satisfiesDualityAt_wrightFisherDual` obtained by evaluating the duality function on the
-- one-dimensional state `u ↦ u 0`.
/-- The Wright--Fisher moment duality identity of Example 26.29:
`E_x[X_t^n] = E_n[x^{Y_t}]`. -/
theorem wrightFisherMoment_eq_dualExpectation
    (L : WFSolution) (hγ : 0 ≤ γ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hL_mem : ∀ ω : L.Ω, ∀ t : NNReal, L ω t 0 ∈ Set.Icc (0 : ℝ) 1)
    {Ω' : Type u} [MeasurableSpace Ω']
    {κ : NNReal → Kernel ℕ ℕ} {Q : ℕ → ProbabilityMeasure Ω'}
    {Y : NNReal → Ω' → ℕ}
    [IsMarkovProcessRealization κ Q Y]
    (hY_generator : HasGeneratorMatrix κ (wrightFisherDualQMatrix γ))
    (n : ℕ) (t : NNReal) :
    wrightFisherMoment L n t = ∫ ω, x ^ (Y t ω) ∂(Q n) := sorry

-- Proof sketch: the stopped Wright--Fisher diffusion is a bounded martingale, so its first moment
-- is constant in time and equal to the deterministic initial value `x`.
/-- The first moment of a Wright--Fisher weak solution stays equal to the initial state. -/
theorem wrightFisherMoment_one (L : WFSolution) :
    wrightFisherMoment L 1 = fun _ ↦ x := sorry

-- Proof sketch: for `γ ≥ 0`, apply Itô's formula to `u ↦ u^n` along the solution path, use the
-- explicit coefficient `sqrt (γ X_t (1 - X_t))` on the invariant interval `[0,1]`, and then take
-- expectations to obtain the recursive Volterra equation for the moments.
/-- For `γ ≥ 0`, if a Wright--Fisher weak solution remains in `[0,1]`, then its moments satisfy
the recursive integral equations from formula `(26.28)`. -/
theorem wrightFisherMoment_recursion
    (L : WFSolution)
    (hγ : 0 ≤ γ)
    (hL_mem : ∀ ω : L.Ω, ∀ t : NNReal, L ω t 0 ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (hn : 2 ≤ n) (t : NNReal) :
    wrightFisherMoment L n t =
      x ^ n +
        γ * (Nat.choose n 2 : ℝ) *
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            (wrightFisherMoment L (n - 1) s.toNNReal - wrightFisherMoment L n s.toNNReal) := sorry

-- Proof sketch: outside the interval `[0,1]` the diffusion coefficient vanishes identically. The
-- stopped process therefore has zero quadratic variation until it could hit `[0,1]`, forcing the
-- path to remain equal to the initial value for all times.
/-- Any Wright--Fisher weak solution started outside `[0,1]` is constant. -/
theorem wrightFisherWeakSolution_constant_of_not_mem_unitInterval
    (hx : x ∉ Set.Icc (0 : ℝ) 1) (L : WFSolution) (ω : L.Ω) (t : NNReal) :
    L ω t = oneDimensionalState x := sorry

end WrightFisher

section WrightFisherGlobal

variable {γ x : ℝ}

local notation "PathSpace" => EuclideanPathSpace 1
local notation "σWF" => oneDimensionalDiffusion (wrightFisherScalarDiffusionCoeff γ)
local notation "bWF" => oneDimensionalDrift (fun _ _ ↦ (0 : ℝ))
local notation "CoordinateProcess" =>
  fun t ↦ (ContinuousMap.evalCLM ℝ t : PathSpace → State)

-- Proof sketch: choose, for each deterministic state `x`, a canonical path-space solution of the
-- Wright--Fisher local martingale problem, apply
-- `canonicalPathProcess_hasStrongMarkovProperty_of_localMartingaleProblemWellPosed` to the
-- resulting family of path laws, and then recover the corresponding weak solutions via
-- `exists_weakSDESolution_with_statePathLaw_of_localMartingaleProblemWellPosed`.
/-- Companion to Example 26.29: the Dirac-initial Wright--Fisher weak-solution family admits a
canonical time-homogeneous strong-Markov realization on path space already under the weaker
hypothesis `γ ≥ 0`. -/
theorem wrightFisher_existsStrongMarkovSolutionFamily_nonneg (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ (P : State → ProbabilityMeasure PathSpace)
      (pathKernel : Kernel State (NNReal → State)),
      (∀ x : State,
        ∃ L :
            GeneralizedWeakSDESolution
              (Measure.dirac x)
              σWF bWF,
          L.IsWeaklyUnique ∧ L.statePathLaw = (P x : Measure PathSpace)) ∧
        IsTimeHomogeneousMarkovProcess CoordinateProcess P pathKernel ∧
        HasStrongMarkovProperty P CoordinateProcess pathKernel := sorry

-- Proof sketch: apply the nonnegative-parameter companion theorem with `0 ≤ γ` coming from
-- `hγ : 0 < γ`. This restores the textbook parameter range on the main source-facing surface.
/-- Example 26.29: for `γ > 0`, the family of Dirac-initial Wright--Fisher weak solutions admits
a canonical time-homogeneous strong-Markov realization on path space. -/
theorem wrightFisher_existsStrongMarkovSolutionFamily (γ : ℝ) (hγ : 0 < γ) :
    ∃ (P : State → ProbabilityMeasure PathSpace)
      (pathKernel : Kernel State (NNReal → State)),
      (∀ x : State,
        ∃ L :
            GeneralizedWeakSDESolution
              (Measure.dirac x)
              σWF bWF,
          L.IsWeaklyUnique ∧ L.statePathLaw = (P x : Measure PathSpace)) ∧
        IsTimeHomogeneousMarkovProcess CoordinateProcess P pathKernel ∧
        HasStrongMarkovProperty P CoordinateProcess pathKernel := by
  simpa using wrightFisher_existsStrongMarkovSolutionFamily_nonneg γ (le_of_lt hγ)

-- Proof sketch: realize the pure-death dual process by `exists_wrightFisherDualProcess`, verify
-- the Wright--Fisher polynomial duality with `satisfiesDualityAt_wrightFisherDual`, and then
-- apply the chapter's canonical duality criterion `localMartingaleProblemWellPosed_of_duality`.
/-- Companion to Example 26.29: for every `γ ≥ 0`, the Wright--Fisher local martingale problem is
well-posed. The strong-Markov realization and weak-solution corollaries below are derived from
this owner-level statement. -/
theorem wrightFisherLocalMartingaleProblemWellPosed (γ : ℝ) (hγ : 0 ≤ γ) :
    LocalMartingaleProblemWellPosed (diffusionMatrixOfCoefficient σWF) bWF := sorry

-- Proof sketch: start from the Dirac-initial solution supplied by the well-posed local
-- martingale problem on `[0,1]`, then use continuity and the vanishing coefficient outside the
-- interval to keep the process in `[0,1]`. Weak uniqueness is the path-space uniqueness inherited
-- from `wrightFisherLocalMartingaleProblemWellPosed`.
/-- A Wright--Fisher weak solution started from `x ∈ [0,1]` can be chosen to stay in `[0,1]` for
all times, and this realization is unique in law, already for `γ ≥ 0`. -/
theorem exists_wrightFisherWeakSolution_in_unitInterval
    (γ x : ℝ) (hγ : 0 ≤ γ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ L :
        GeneralizedWeakSDESolution
          (Measure.dirac (oneDimensionalState x))
          σWF bWF,
      L.IsWeaklyUnique ∧
        ∀ ω : L.Ω, ∀ t : NNReal, L ω t 0 ∈ Set.Icc (0 : ℝ) 1 := sorry

-- Proof sketch: combine the owner-level well-posedness theorem
-- `wrightFisherLocalMartingaleProblemWellPosed` with the standard SDE/local-martingale-problem
-- bridge. If `x ∈ [0,1]`, one may also use
-- `exists_wrightFisherWeakSolution_in_unitInterval`; if `x ∉ [0,1]`, every weak solution is
-- constant by `wrightFisherWeakSolution_constant_of_not_mem_unitInterval`.
/-- Corollary of Example 26.29: for every `γ ≥ 0` and every deterministic initial state
`x ∈ ℝ`, the Wright--Fisher SDE admits a weak solution, and this weak solution is unique in law.
-/
theorem exists_wrightFisherWeakSolution_isWeaklyUnique
    (γ x : ℝ) (hγ : 0 ≤ γ) :
    ∃ L :
        GeneralizedWeakSDESolution
          (Measure.dirac (oneDimensionalState x))
          σWF bWF,
      L.IsWeaklyUnique := sorry

end WrightFisherGlobal

end ProbabilityTheory
