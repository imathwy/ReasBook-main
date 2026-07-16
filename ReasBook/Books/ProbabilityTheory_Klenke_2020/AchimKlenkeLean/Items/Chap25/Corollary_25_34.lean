import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap25.Theorem_25_33

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Laplacian InnerProductSpace

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "VectorProcess" => NNReal → Ω → State

-- Proof sketch: for the forward direction, harmonicity on all of `State` implies that the
-- Laplacian vanishes in a neighborhood of every point, hence everywhere. For the reverse
-- direction, use the `C²` hypothesis `hF` and the pointwise identity `Δ F = 0` to package the
-- defining pair of conditions for `InnerProductSpace.HarmonicOnNhd`.
/-- For a `C²` function on `State`, global harmonicity is equivalent to the vanishing of the
Laplacian everywhere. -/
private theorem harmonicOnNhd_univ_iff_laplacian_eq_zero
    {F : State → ℝ} (hF : ContDiff ℝ 2 F) :
    HarmonicOnNhd F Set.univ ↔ Δ F = 0 := sorry

-- Proof sketch: apply the multidimensional Brownian Itô formula from the preceding theorem to the
-- `C²` function `F`. If `F` is harmonic, the drift term `½ ∫₀ᵗ ΔF(W_s) ds` vanishes, leaving a
-- continuous local martingale. Conversely, if `F(W_t)` is a continuous local martingale, subtract
-- the Itô martingale term to obtain a continuous finite-variation local martingale, which must be
-- constant; therefore the drift integral vanishes for every `t`, forcing `Δ F = 0`, hence
-- harmonicity by `harmonicOnNhd_univ_iff_laplacian_eq_zero`.
section

variable {W : VectorProcess} (hW : IsStandardBrownianMotionVector μ W)

local notation "ℱW" => Filtration.natural W hW.stronglyMeasurable

/-- Corollary 25.34: for a standard `d`-dimensional Brownian motion `W` and a `C²` function
`F : State → ℝ`, the process `(F(W_t))_{t ≥ 0}` is a continuous local martingale with respect to
the natural filtration of `W` if and only if `F` is harmonic. -/
theorem brownian_comp_continuousLocalMartingale_iff_harmonic
    {F : State → ℝ} (hF : ContDiff ℝ 2 F) :
    IsContinuousLocalMartingale ℱW μ (fun t ω ↦ F (W t ω)) ↔
      HarmonicOnNhd F Set.univ := sorry

end

end ProbabilityTheory
