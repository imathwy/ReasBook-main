import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_26_3_1 (from Items/Chap26) -/
open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

/-- The Galton--Watson branching process started from `x` and driven by the offspring array `Y`.
The next generation is the sum of the offspring counts of the currently alive particles. -/
def branchingProcess (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) : ℕ → Ω → ℕ
  | 0 => fun _ ↦ x
  | n + 1 => fun ω ↦ Finset.sum (Finset.range (branchingProcess x Y n ω)) (fun i ↦ Y n i ω)

-- Proof sketch: unfold the recursive definition of `branchingProcess` at time `0`.
/-- The branching process starts from the deterministic initial population `x`. -/
theorem branchingProcess_zero (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) :
    branchingProcess x Y 0 = fun _ ↦ x := rfl

section Measurable

variable [MeasurableSpace Ω]

-- Proof sketch: use the canonical CIR Laplace transform `cirLaplaceTransform γ t z` from
-- Example 26.11 for the one-time marginal `Zt` under the one-time law `Pz`, send the Laplace
-- parameter to `+∞`, and identify the limit of `E[e^{-λ Zt}]` with the extinction probability
-- `Pz[Zt = 0]`.
/-- Exercise 26.3.1 (1): if the solution of `dZ_t = sqrt (γ Z_t) dW_t` started from `z` has
the explicit CIR/Feller branching Laplace transform, then its extinction probability at time `t`
is `exp (-2 z / (γ t))`. -/
theorem fellerBranchingDiffusion_extinctionProbability_eq
    (Pz : ProbabilityMeasure Ω) (Zt : Ω → NNReal)
    {γ z t : NNReal} (hγ : 0 < γ) (ht : 0 < t)
    (hLaplace : ∀ l : NNReal,
      ∫ ω, Real.exp (-((l : ℝ) * (Zt ω : ℝ))) ∂(Pz : Measure Ω) =
        cirLaplaceTransform γ t z l) :
    (Pz : Measure Ω) {ω | Zt ω = 0} =
      ENNReal.ofReal (Real.exp (-(2 * (z : ℝ)) / ((γ : ℝ) * (t : ℝ)))) := sorry

-- Proof sketch: write the extinction-by-generation-`n` probability as the `N`th power of the
-- one-ancestor extinction approximation, apply Lemma 21.44 at `s = 0` to compute the `n`th pgf
-- iterate of the canonical critical geometric offspring law, and then use independence of the
-- `N` initial lineages.
/-- Exercise 26.3.1 (2): for a Galton--Watson branching process started from `N` particles with
critical geometric offspring law, the probability of being extinct by generation `n` is
`(n / (n + 1))^N`. -/
theorem criticalGeometric_galtonWatson_extinctByTime_eq
    (P : ProbabilityMeasure Ω) (N n : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law :
      ∀ k i, HasLaw (Y k i) criticalGeometricOffspringPMF.toMeasure (P : Measure Ω)) :
    ((P : Measure Ω) {ω | branchingProcess N Y n ω = 0}) =
      ENNReal.ofReal (((n : ℝ) / ((n : ℝ) + 1)) ^ N) := sorry

end Measurable

end ProbabilityTheory

/-! ### Remark_26_3 (from Items/Chap26) -/
open MeasureTheory ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {n m : ℕ}

local notation "State" => Fin n → ℝ
local notation "StatePath" => EuclideanPathSpace n
local notation "NoisePath" => EuclideanPathSpace m

/- Domain-style sampling for Remark 26.3:
* primary domain: pathwise strong solutions of SDEs on filtered spaces carrying Brownian drivers;
* sampled owner declarations: `StrongSolutionOperator`, `StrongSolution`,
  `strongSolution_iff_exists_solver`, and `Function.toEuclidean`;
* core/canonical owner: `StrongSolution` with realized paths coming from
  `StrongSolutionOperator.realization`;
* bridge/view layer here: transfer a pathwise solver hypothesis on arbitrary Brownian realizations
  into the canonical `StrongSolution` owner;
* primitive data: the Brownian/adaptedness/independence/initial measurability hypotheses together
  with the equation-solving clause for `F.realization`;
* derived API: the resulting `StrongSolution` witness.
-/
/-- Remark 26.3: a pathwise strong-solution operator produces, on every filtered space carrying an
independent Brownian driver and initial datum, a realized strong solution of the same integral
equation. -/
theorem realization_isStrongSolution_on_any_brownian_realization
    {F : StrongSolutionOperator n m}
    {Equation : {Ω : Type u} → [MeasurableSpace Ω] →
      (Ω → State) → (Ω → NoisePath) → (Ω → StatePath) → Prop}
    (hF : ∀ {Ω : Type u} [MeasurableSpace Ω]
      (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
      (μ : Measure Ω) (ξ : Ω → State) (W : Ω → NoisePath),
      IsStandardBrownianMotionVector μ (Function.toEuclidean (fun t ω ↦ W ω t)) →
      Adapted ℱ (fun t ω ↦ W ω t) →
      IndepFun ξ W μ →
      Measurable[ℱ 0] ξ →
      Equation ξ W (F.realization ξ W))
    {Ω : Type u} [MeasurableSpace Ω]
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω) (ξ : Ω → State) (W : Ω → NoisePath)
    (hW : IsStandardBrownianMotionVector μ (Function.toEuclidean (fun t ω ↦ W ω t)))
    (hW_adapted : Adapted ℱ (fun t ω ↦ W ω t))
    (hξW : IndepFun ξ W μ)
    (hξ : Measurable[ℱ 0] ξ) :
    StrongSolution n m Equation ξ W (F.realization ξ W) := by
  refine strongSolution_iff_exists_solver.2 ?_
  exact ⟨F, rfl, hF ℱ μ ξ W hW hW_adapted hξW hξ⟩

end ProbabilityTheory
