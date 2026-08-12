import Mathlib
import ProbabilityTheory_Klenke_2020.Chap21.Corollary_21_73
import ProbabilityTheory_Klenke_2020.Chap25.StandardBrownianMotionVector
import ProbabilityTheory_Klenke_2020.Chap25.Theorem_25_27
import ProbabilityTheory_Klenke_2020.Chap25.Theorem_25_30

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open Laplacian InnerProductSpace
open scoped BigOperators Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {d : ℕ}

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "Process" => NNReal → Ω → ℝ
local notation "VectorProcess" => NNReal → Ω → State
local notation "MatrixProcess" => NNReal → Ω → Fin d → Fin d → ℝ
local notation "ProcessVector" => Fin d → Process

variable {ℱ : TimeFiltration}

/-- The canonical coordinate martingale part
`Mᵏ_t = Y_t^k - ∫_0^t b_s^k ds`
of the generalized diffusion `Y`. -/
def generalizedDiffusionCoordinateMartingalePart
    (b Y : VectorProcess) (k : Fin d) : Process :=
  fun t ω ↦ Y t ω k - ∫ s in Set.Icc (0 : ℝ) (t : ℝ), b s.toNNReal ω k

-- Proof sketch: identify the canonical Euclidean-space Laplacian with the sum of the second
-- derivatives along the standard coordinate basis vectors, and then rewrite those basis
-- derivatives using the coordinate partial derivatives from Theorem 25.30.
/-- For the coordinate model `State = ℝ^d`, the canonical Euclidean Laplacian is the sum of the
diagonal second coordinate derivatives. This is the coordinate bridge for the textbook formula,
while the main Brownian Itô statement below uses the canonical operator `Δ`. -/
theorem laplacian_eq_sum_secondPartialDeriv
    (F : State → ℝ) (x : State) :
    Δ F x =
      ∑ k : Fin d, (∂²[k, k] F) x := sorry

-- Proof sketch: write the canonical coordinate martingale parts as
-- `Mᵏ_t = Y_t^k - ∫_0^t b_s^k ds`, apply the one-dimensional Itô formula of Theorem 25.27 to the
-- stochastic integrals `∫_0^t ∂ₖ F(Y_s) dM_s^k`, and use the quadratic-covariation hypotheses to
-- rewrite the second-order correction by the density field `a`.
/-- Theorem 25.33 (1): let
`Mᵏ_t = Y_t^k - ∫_0^t b_s^k ds`
be the canonical coordinate martingale parts of the generalized diffusion `Y`. If `Nᵏ` realizes
`∫_0^t ∂ₖ F(Y_s) dM_s^k` and the quadratic covariations satisfy
`⟨Mᵏ,Mˡ⟩_t = ∫_0^t a_s^{k,l} ds`, then the multidimensional Itô formula holds:
`F (Y_T) - F (Y_0)` agrees, for each deterministic time almost surely, with the stochastic term
`∑ₖ Nᵏ_T`, the drift term `∑ₖ ∫_0^T b_s^k ∂ₖ F(Y_s) ds`, and the quadratic correction
`(1/2) \sum_{k,l} ∫_0^T a_s^{k,l} ∂ₖ∂ₗ F(Y_s) ds`. The Brownian realization data from the
generalized-diffusion definition is already absorbed into these owner-level martingale and
covariation hypotheses, so the project API states the result directly in terms of them as an
equality of modifications. -/
theorem multidimensionalGeneralizedDiffusion_ito_formula
    (F : State → ℝ) (hF : ContDiff ℝ 2 F)
    {a : MatrixProcess} {b Y : VectorProcess}
    {N : ProcessVector}
    (hM :
      ∀ k : Fin d,
        IsContinuousLocalMartingale ℱ μ
          (generalizedDiffusionCoordinateMartingalePart b Y k))
    (hMbr :
      ∀ k : Fin d,
        HasAbsolutelyContinuousSquareVariation
          (generalizedDiffusionCoordinateMartingalePart b Y k)
          (hM k))
    (hIto :
      ∀ k : Fin d,
        IsContinuousLocalMartingaleItoIntegral
          (hMbr k)
          (fun t ω ↦ (∂[k] F) (Y t ω))
          (N k))
    (hCovariation :
      ∀ k l : Fin d,
        IsContinuousQuadraticCovariationProcess
          ℱ
          μ
          (generalizedDiffusionCoordinateMartingalePart b Y k)
          (generalizedDiffusionCoordinateMartingalePart b Y l)
          (fun t ω ↦
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ), a s.toNNReal ω k l))
    (hb : ∀ k : Fin d, ProgMeasurable ℱ (fun t ω ↦ b t ω k))
    (hint :
      ∀ k : Fin d, ∀ T : NNReal, ∀ᵐ ω ∂μ,
        IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω k|) (Set.Icc (0 : ℝ) (T : ℝ))) :
    AreModifications μ
      (fun T ω ↦ F (Y T ω) - F (Y 0 ω))
      (fun T ω ↦
        (∑ k : Fin d, N k T ω) +
          (∑ k : Fin d,
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
              b s.toNNReal ω k * (∂[k] F) (Y s.toNNReal ω)) +
          ((1 : ℝ) / 2) *
            ∑ k : Fin d, ∑ l : Fin d,
              ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
                a s.toNNReal ω k l *
                  (∂²[k, l] F) (Y s.toNNReal ω)) := sorry

set_option linter.unusedVariables false in
/-- The fixed-time almost-sure form of Theorem 25.33 (1). -/
theorem multidimensionalGeneralizedDiffusion_ito_formula_ae_eq
    (F : State → ℝ) (hF : ContDiff ℝ 2 F)
    {a : MatrixProcess} {b Y : VectorProcess}
    {N : ProcessVector}
    (hM :
      ∀ k : Fin d,
        IsContinuousLocalMartingale ℱ μ
          (generalizedDiffusionCoordinateMartingalePart b Y k))
    (hMbr :
      ∀ k : Fin d,
        HasAbsolutelyContinuousSquareVariation
          (generalizedDiffusionCoordinateMartingalePart b Y k)
          (hM k))
    (hIto :
      ∀ k : Fin d,
        IsContinuousLocalMartingaleItoIntegral
          (hMbr k)
          (fun t ω ↦ (∂[k] F) (Y t ω))
          (N k))
    (hCovariation :
      ∀ k l : Fin d,
        IsContinuousQuadraticCovariationProcess
          ℱ
          μ
          (generalizedDiffusionCoordinateMartingalePart b Y k)
          (generalizedDiffusionCoordinateMartingalePart b Y l)
          (fun t ω ↦
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ), a s.toNNReal ω k l))
    (hb : ∀ k : Fin d, ProgMeasurable ℱ (fun t ω ↦ b t ω k))
    (hint :
      ∀ k : Fin d, ∀ T : NNReal, ∀ᵐ ω ∂μ,
        IntegrableOn (fun s : ℝ ↦ |b s.toNNReal ω k|) (Set.Icc (0 : ℝ) (T : ℝ)))
    (T : NNReal) :
    (fun ω ↦ F (Y T ω) - F (Y 0 ω))
      =ᵐ[μ]
        (fun ω ↦
          (∑ k : Fin d, N k T ω) +
            (∑ k : Fin d,
              ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
                b s.toNNReal ω k * (∂[k] F) (Y s.toNNReal ω)) +
            ((1 : ℝ) / 2) *
              ∑ k : Fin d, ∑ l : Fin d,
                ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
                  a s.toNNReal ω k l *
                    (∂²[k, l] F) (Y s.toNNReal ω)) :=
  multidimensionalGeneralizedDiffusion_ito_formula
    F hF hM hMbr hIto hCovariation hb hint T

-- Proof sketch: specialize part (1) to the Brownian diffusion with zero drift and identity
-- covariance matrix, then rewrite the quadratic correction with the canonical Euclidean
-- Laplacian `Δ`.
/-- Theorem 25.33 (2): for a `d`-dimensional Brownian motion `W` with independent coordinates, the
multidimensional Itô formula reduces to
`F (W_t) - F (W_0) = ∑ₖ ∫₀ᵗ ∂ₖ F (W_s) dW_s^k + (1/2) ∫₀ᵗ ΔF (W_s) ds`.
In Lean this is stated with the canonical Laplacian `Δ F`. This is stated as an
equality of modifications, with a fixed-time almost-sure corollary below. -/
theorem brownian_multidimensional_ito_formula
    (F : State → ℝ) (hF : ContDiff ℝ 2 F)
    {W : VectorProcess} {N : ProcessVector}
    (hW : IsStandardBrownianMotionVector μ W)
    (hWeighted :
      ∀ k : Fin d,
        IsBrownianLocalItoIntegral
          ℱ
          μ
          (fun t ω ↦ W t ω k)
          (fun t ω ↦ (∂[k] F) (W t ω))
          (N k)) :
    AreModifications μ
      (fun t ω ↦ F (W t ω) - F (W 0 ω))
      (fun t ω ↦
        (∑ k : Fin d, N k t ω) +
          ((1 : ℝ) / 2) *
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              Δ F (W s.toNNReal ω)) := sorry

set_option linter.unusedVariables false in
/-- The fixed-time almost-sure form of Theorem 25.33 (2). -/
theorem brownian_multidimensional_ito_formula_ae_eq
    (F : State → ℝ) (hF : ContDiff ℝ 2 F)
    {W : VectorProcess} {N : ProcessVector}
    (hW : IsStandardBrownianMotionVector μ W)
    (hWeighted :
      ∀ k : Fin d,
        IsBrownianLocalItoIntegral
          ℱ
          μ
          (fun t ω ↦ W t ω k)
          (fun t ω ↦ (∂[k] F) (W t ω))
          (N k))
    (t : NNReal) :
    (fun ω ↦ F (W t ω) - F (W 0 ω))
      =ᵐ[μ]
        (fun ω ↦
          (∑ k : Fin d, N k t ω) +
            ((1 : ℝ) / 2) *
              ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
                Δ F (W s.toNNReal ω)) :=
  brownian_multidimensional_ito_formula F hF hW hWeighted t

end ProbabilityTheory
