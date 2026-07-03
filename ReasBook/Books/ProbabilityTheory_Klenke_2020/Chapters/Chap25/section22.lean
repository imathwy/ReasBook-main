import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_25_22 (from Items/Chap25) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

variable {ℱ : TimeFiltration}
variable {M H N : Fin 2 → Process}

-- Proof sketch: apply Theorem 25.21 separately to the two source-facing Itô-integral realizations
-- `Nⁱ` encoded by `IsContinuousLocalMartingaleItoIntegral (hbr i) (H i) (N i)`.
/-- Theorem 25.22 (1): for `i = 1, 2`, if `Nⁱ_t = ∫_0^t H_s^i \, dM_s^i` is realized by the
canonical relation `IsContinuousLocalMartingaleItoIntegral`, then `Nⁱ` is again a continuous
local martingale. -/
theorem stochasticIntegral_family_isContinuousLocalMartingale
    (hM : ∀ i : Fin 2, IsContinuousLocalMartingale ℱ μ (M i))
    (hbr : ∀ i : Fin 2, HasAbsolutelyContinuousSquareVariation (M i) (hM i))
    (hN : ∀ i : Fin 2, IsContinuousLocalMartingaleItoIntegral (hbr i) (H i) (N i))
    : ∀ i : Fin 2, IsContinuousLocalMartingale ℱ μ (N i) := sorry

-- Proof sketch: by part (1), each `Nⁱ` belongs to `Mlocc ℱ μ`; then apply Corollary 21.73 to
-- each pair `(Nⁱ, Nʲ)`.
/-- Theorem 25.22 (2): for `i, j ∈ {1, 2}`, the stochastic integrals
`Nⁱ_t = ∫_0^t H_s^i \, dM_s^i` and `Nʲ_t = ∫_0^t H_s^j \, dM_s^j` admit a unique continuous
quadratic-covariation process. -/
theorem stochasticIntegral_family_existsUnique_continuousQuadraticCovariationProcess
    (hM : ∀ i : Fin 2, IsContinuousLocalMartingale ℱ μ (M i))
    (hbr : ∀ i : Fin 2, HasAbsolutelyContinuousSquareVariation (M i) (hM i))
    (hN : ∀ i : Fin 2, IsContinuousLocalMartingaleItoIntegral (hbr i) (H i) (N i))
    :
    ∀ i j : Fin 2,
      ∃! A : Process, IsContinuousQuadraticCovariationProcess ℱ μ (N i) (N j) A := sorry

-- Proof sketch: assume the bracket of `(Mⁱ, Mʲ)` is already realized by the displayed density
-- formula, then identify the bracket of the Itô integrals with the corresponding weighted density
-- formula `∫ Hⁱ Hʲ aⁱʲ ds`.
/-- Theorem 25.22 (3): for `i, j ∈ {1, 2}`, if the quadratic covariation of `Mⁱ` and `Mʲ` is
given by the density `aⁱʲ`, then the quadratic covariation of the Itô integrals is given by
`⟨Nⁱ, Nʲ⟩_t = ∫_0^t H_s^i H_s^j a_sⁱʲ \, ds`. -/
theorem stochasticIntegral_family_covariation_formula
    (hM : ∀ i : Fin 2, IsContinuousLocalMartingale ℱ μ (M i))
    (hbr : ∀ i : Fin 2, HasAbsolutelyContinuousSquareVariation (M i) (hM i))
    (hN : ∀ i : Fin 2, IsContinuousLocalMartingaleItoIntegral (hbr i) (H i) (N i))
    {covDensity : Fin 2 → Fin 2 → Process}
    (hMN_covariation :
      ∀ i j : Fin 2,
        IsContinuousQuadraticCovariationProcess
          ℱ μ
          (M i)
          (M j)
          (driftIntegralProcess (covDensity i j))) :
    ∀ i j : Fin 2,
      IsContinuousQuadraticCovariationProcess
        ℱ μ
        (N i)
        (N j)
        (driftIntegralProcess fun t ω ↦ H i t ω * H j t ω * covDensity i j t ω) := sorry

-- Proof sketch: use the independent-integrator hypothesis directly at the source level to obtain
-- vanishing mixed bracket for `(M¹, M²)`, and then specialize part (3) to the zero density.
/-- Theorem 25.22 (4): if `M¹` and `M²` are independent, then the mixed quadratic covariation of
the stochastic integrals `N¹_t = ∫_0^t H_s^1 \, dM_s^1` and `N²_t = ∫_0^t H_s^2 \, dM_s^2`
vanishes identically. -/
theorem stochasticIntegral_crossCovariation_eq_zero_of_indep
    (hM : ∀ i : Fin 2, IsContinuousLocalMartingale ℱ μ (M i))
    (hbr : ∀ i : Fin 2, HasAbsolutelyContinuousSquareVariation (M i) (hM i))
    (hN : ∀ i : Fin 2, IsContinuousLocalMartingaleItoIntegral (hbr i) (H i) (N i))
    (hindep : IndepFun (fun ω t ↦ M 0 t ω) (fun ω t ↦ M 1 t ω) μ) :
    IsContinuousQuadraticCovariationProcess ℱ μ (N 0) (N 1) 0 := sorry

end ProbabilityTheory
