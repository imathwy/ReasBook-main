import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_26_20 (from Items/Chap26) -/
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {n : ℕ}

local notation "State" => Fin n → ℝ
local notation "PathSpace" => EuclideanPathSpace n
local notation "DiffusionMatrixCoeff" => NNReal → State → Fin n → Fin n → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

section FixedSpace

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal mΩ

/-- The `i`-th drift-compensated coordinate process attached to a path-valued process `X`. -/
def localMartingaleProblemMartingalePart
    (b : DriftCoeff) (X : Ω → PathSpace) (i : Fin n) : NNReal → Ω → ℝ :=
  fun t ω ↦ X ω t i - ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (X ω s.toNNReal) i

-- Proof sketch: unfold `localMartingaleProblemMartingalePart`; it is defined by subtracting the
-- time-integrated drift from the `i`-th coordinate of the path-valued process.
/-- Evaluating the martingale part gives the `i`-th coordinate minus its drift integral. -/
theorem localMartingaleProblemMartingalePart_apply
    (b : DriftCoeff) (X : Ω → PathSpace) (i : Fin n) (t : NNReal) (ω : Ω) :
    localMartingaleProblemMartingalePart b X i t ω =
      X ω t i - ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal (X ω s.toNNReal) i := sorry

/-- The prescribed quadratic-covariation process for coordinates `i` and `j` in the local
martingale problem with coefficient field `a`. -/
def localMartingaleProblemCovariation
    (a : DiffusionMatrixCoeff) (X : Ω → PathSpace) (i j : Fin n) : NNReal → Ω → ℝ :=
  fun t ω ↦ ∫ s in Set.Icc (0 : ℝ) (t : ℝ), a s.toNNReal (X ω s.toNNReal) i j

-- Proof sketch: unfold `localMartingaleProblemCovariation`; it is the time integral of the
-- `(i,j)`-entry of `a` evaluated along the sample path `X`.
/-- Evaluating the prescribed covariation gives the time integral of `aᵢⱼ(s, X_s)`. -/
theorem localMartingaleProblemCovariation_apply
    (a : DiffusionMatrixCoeff) (X : Ω → PathSpace) (i j : Fin n) (t : NNReal) (ω : Ω) :
    localMartingaleProblemCovariation a X i j t ω =
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), a s.toNNReal (X ω s.toNNReal) i j := sorry

/-- Definition 26.20: a continuous `n`-dimensional path-valued process `X` solves the local
martingale problem `LMP(a, b, μ₀)` if its initial law is `μ₀` and each drift-compensated
coordinate is a continuous local martingale whose quadratic covariation with every other
coordinate is given by the integral of `a` along `X`. -/
structure IsLocalMartingaleProblemSolution
    (μ₀ : Measure State) [IsProbabilityMeasure μ₀]
    (a : DiffusionMatrixCoeff) (b : DriftCoeff)
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (X : Ω → PathSpace) : Prop where
  /-- The initial distribution of the solution is `μ₀`. -/
  initial_law : HasLaw (fun ω ↦ X ω 0) μ₀ μ
  /-- Each drift-compensated coordinate is a continuous local martingale. -/
  martingalePart :
    letI : IsProbabilityMeasure μ := initial_law.isProbabilityMeasure
    ∀ i : Fin n, IsContinuousLocalMartingale ℱ μ (localMartingaleProblemMartingalePart b X i)
  /-- The quadratic covariation of the `i`-th and `j`-th martingale parts is the prescribed
  integral of `aᵢⱼ` along the path `X`. -/
  quadraticCovariation :
    letI : IsProbabilityMeasure μ := initial_law.isProbabilityMeasure
    ∀ i j : Fin n,
      IsContinuousQuadraticCovariationProcess ℱ μ
        (localMartingaleProblemMartingalePart b X i)
        (localMartingaleProblemMartingalePart b X j)
        (localMartingaleProblemCovariation a X i j)

namespace IsLocalMartingaleProblemSolution

/-- Any local-martingale-problem solution is carried by a probability measure because its initial
law is the probability measure `μ₀`. -/
theorem isProbabilityMeasure
    {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    {a : DiffusionMatrixCoeff} {b : DriftCoeff}
    {ℱ : TimeFiltration} {μ : Measure Ω} {X : Ω → PathSpace}
    (hX : IsLocalMartingaleProblemSolution μ₀ a b ℱ μ X) :
    IsProbabilityMeasure μ :=
  hX.initial_law.isProbabilityMeasure

/-- The `Mlocc` formulation of the martingale clause is a derived set-level view of the owner
predicate `IsContinuousLocalMartingale`. -/
theorem martingale_part_mem_Mlocc
    {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    {a : DiffusionMatrixCoeff} {b : DriftCoeff}
    {ℱ : TimeFiltration} {μ : Measure Ω}
    {X : Ω → PathSpace}
    (hX : IsLocalMartingaleProblemSolution μ₀ a b ℱ μ X) (i : Fin n) :
    localMartingaleProblemMartingalePart b X i ∈ Mlocc ℱ μ := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  exact (mem_Mlocc_iff ℱ μ _).2 (hX.martingalePart i)

end IsLocalMartingaleProblemSolution

/-- A path-valued process is canonically a local-martingale-problem solution once the initial-law,
coordinate local-martingale, and prescribed quadratic-covariation clauses are given. -/
instance
    (μ₀ : Measure State) [IsProbabilityMeasure μ₀]
    (a : DiffusionMatrixCoeff) (b : DriftCoeff)
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (X : Ω → PathSpace)
    (hinitialLaw : HasLaw (fun ω ↦ X ω 0) μ₀ μ)
    (hmartingalePart :
      letI : IsProbabilityMeasure μ := hinitialLaw.isProbabilityMeasure
      ∀ i : Fin n, IsContinuousLocalMartingale ℱ μ (localMartingaleProblemMartingalePart b X i))
    (hquadraticCovariation :
      letI : IsProbabilityMeasure μ := hinitialLaw.isProbabilityMeasure
      ∀ i j : Fin n,
        IsContinuousQuadraticCovariationProcess ℱ μ
          (localMartingaleProblemMartingalePart b X i)
          (localMartingaleProblemMartingalePart b X j)
          (localMartingaleProblemCovariation a X i j)) :
    IsLocalMartingaleProblemSolution μ₀ a b ℱ μ X where
  initial_law := hinitialLaw
  martingalePart := hmartingalePart
  quadraticCovariation := hquadraticCovariation

/-- The local martingale problem `LMP(a, b, μ₀)` is unique when any two of its solutions have the
same law on continuous path space. -/
def LocalMartingaleProblemHasUniqueLaw
    (μ₀ : Measure State) [IsProbabilityMeasure μ₀]
    (a : DiffusionMatrixCoeff) (b : DriftCoeff) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω]
      (ℱ : Filtration NNReal mΩ) (μ : Measure Ω) (X : Ω → PathSpace)
      {Ω' : Type v} [mΩ' : MeasurableSpace Ω']
      (ℱ' : Filtration NNReal mΩ') (μ' : Measure Ω')
      (X' : Ω' → PathSpace),
      IsLocalMartingaleProblemSolution μ₀ a b ℱ μ X →
      IsLocalMartingaleProblemSolution μ₀ a b ℱ' μ' X' →
      μ.map X = μ'.map X'

end FixedSpace

section DiffusionMatrix

variable {m : ℕ}

local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin m → ℝ

/-- The diffusion matrix field `a = σσᵀ` associated with a coefficient field `σ`. -/
def diffusionMatrixOfCoefficient (σ : DiffusionCoeff) : DiffusionMatrixCoeff :=
  fun t x i j ↦ ∑ k : Fin m, σ t x i k * σ t x j k

section

variable (σ : DiffusionCoeff)

local notation "σσᵀ" => diffusionMatrixOfCoefficient σ

-- Proof sketch: unfold `σσᵀ`; the value at `(t, x, i, j)` is the defining finite sum over the
-- common noise index `k`.
/-- Evaluating `σσᵀ` gives the coefficient sum `∑ₖ σᵢₖ σⱼₖ`. -/
theorem diffusionMatrixOfCoefficient_apply
    (t : NNReal) (x : State) (i j : Fin n) :
    σσᵀ t x i j = ∑ k : Fin m, σ t x i k * σ t x j k := rfl

-- Proof sketch: unfold `σσᵀ`; the sum over `k` is manifestly symmetric in the two outer indices
-- after swapping the two scalar factors.
/-- The matrix field `σσᵀ` is symmetric in the indices `i` and `j`. -/
theorem diffusionMatrixOfCoefficient_symmetric
    (t : NNReal) (x : State) (i j : Fin n) :
    σσᵀ t x i j = σσᵀ t x j i := sorry

-- Proof sketch: rewrite the quadratic form using the definition of `σσᵀ` and identify it with
-- the finite sum `∑ k, (∑ i, v i * σ t x i k)^2`, which is termwise nonnegative.
/-- The matrix field `σσᵀ` is nonnegative semidefinite through its quadratic form. -/
theorem diffusionMatrixOfCoefficient_quadraticForm_nonneg
    (t : NNReal) (x v : State) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, v i * σσᵀ t x i j * v j := sorry

end

end DiffusionMatrix

end ProbabilityTheory
