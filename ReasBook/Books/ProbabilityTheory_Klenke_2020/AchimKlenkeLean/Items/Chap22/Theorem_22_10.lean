import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_2
import ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_42
import ProbabilityTheory_Klenke_2020.Items.Chap22.Theorem_22_9

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/- Theorem 22.10 is `source-facing`: it asserts that a centered square-integrable random variable
arises as the almost-sure and `L²` limit of a martingale whose finite truncations are Chapter 9
binary models. The owner abstraction for the `L²` convergence clause is the Chapter 7 notion
`TendstoInLp 2`; the raw `eLpNorm` formulation is only the derived `bridge/view`. The primitive
data here are the process `Y`, the finite-horizon binary-model property on its truncations, and
the martingale structure for its natural filtration; the `eLpNorm` limit is derived API. -/

-- Proof sketch: use the dyadic sign process built from the comparisons between `X` and the
-- successive conditional expectations `E[X | σ(D₁, …, Dₙ)]`. These conditional expectations form a
-- square-integrable martingale starting at `0`; martingale convergence in `L²` and almost surely
-- yields a limit, and the sign argument identifies that limit with `X`.
/-- Theorem 22.10: every centered square-integrable real random variable is the almost-sure and
`L²` limit of a martingale starting from `0` whose finite truncations are Chapter 9 binary
models. The canonical owner for the `L²` convergence clause is `TendstoInLp 2`. -/
theorem exists_binarySplittingMartingale_tendsto_ae_and_tendstoInLp_two
    {X : Ω → ℝ} (hX_sq : MemLp X 2 μ) (hX_mean_zero : ∫ ω, X ω ∂μ = 0) :
      ∃ Y : ℕ → Ω → ℝ,
      ∃ hY_binary : ∀ T, IsBinaryModel (fun i : Fin (T + 1) ↦ Y i.1),
        let ℱY := Filtration.natural Y
          (ProbabilityTheory.binaryModelTruncations_stronglyMeasurable hY_binary)
        Martingale Y ℱY μ ∧
          Y 0 = 0 ∧
          (∀ᵐ ω ∂μ, Tendsto (fun n ↦ Y n ω) atTop (𝓝 (X ω))) ∧
          TendstoInLp 2 μ Y X := sorry

/-- Bridge companion to Theorem 22.10: the owner-level `TendstoInLp 2` conclusion rewritten as
convergence of the corresponding `eLpNorm` errors. -/
theorem exists_binarySplittingMartingale_tendsto_ae_and_eLpNorm_two
    {X : Ω → ℝ} (hX_sq : MemLp X 2 μ) (hX_mean_zero : ∫ ω, X ω ∂μ = 0) :
      ∃ Y : ℕ → Ω → ℝ,
      ∃ hY_binary : ∀ T, IsBinaryModel (fun i : Fin (T + 1) ↦ Y i.1),
        let ℱY := Filtration.natural Y
          (ProbabilityTheory.binaryModelTruncations_stronglyMeasurable hY_binary)
        Martingale Y ℱY μ ∧
          Y 0 = 0 ∧
          (∀ᵐ ω ∂μ, Tendsto (fun n ↦ Y n ω) atTop (𝓝 (X ω))) ∧
          Tendsto (fun n ↦ eLpNorm (Y n - X) 2 μ) atTop (𝓝 0) := by
  rcases exists_binarySplittingMartingale_tendsto_ae_and_tendstoInLp_two hX_sq hX_mean_zero with
    ⟨Y, hY_binary, hrest⟩
  dsimp at hrest ⊢
  rcases hrest with ⟨hY_mart, hY0, hY_tendsto_ae, hY_tendsto_l2⟩
  exact ⟨Y, hY_binary, hY_mart, hY0, hY_tendsto_ae, hY_tendsto_l2.tendsto_eLpNorm⟩

end ProbabilityTheory
