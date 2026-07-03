import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/-- The index set `[0,1]^d` for the `d`-parameter Brownian sheet. -/
abbrev BrownianSheetIndex (d : ℕ) := Fin d → Set.Icc (0 : ℝ) 1

/-- The covariance kernel `∏ᵢ min (sᵢ, tᵢ)` of the Brownian sheet on `[0,1]^d`. -/
def brownianSheetCovariance {d : ℕ} (s t : BrownianSheetIndex d) : ℝ :=
  ∏ i : Fin d, min (s i : ℝ) (t i : ℝ)

-- Proof sketch: unfold `brownianSheetCovariance`.
/-- Expanding `brownianSheetCovariance` gives the product of the coordinatewise minima. -/
theorem brownianSheetCovariance_def {d : ℕ} (s t : BrownianSheetIndex d) :
    brownianSheetCovariance s t = ∏ i : Fin d, min (s i : ℝ) (t i : ℝ) := sorry

/-- The canonical coordinate process on the Brownian-sheet path space `(BrownianSheetIndex d → ℝ)`.
-/
def brownianSheetCoordinateProcess (d : ℕ) :
    BrownianSheetIndex d → (BrownianSheetIndex d → ℝ) → ℝ :=
  fun t ω ↦ ω t

-- Proof sketch: unfold `brownianSheetCoordinateProcess`.
/-- Evaluating the Brownian-sheet coordinate process at `t` returns the coordinate `ω t`. -/
theorem brownianSheetCoordinateProcess_apply {d : ℕ}
    (t : BrownianSheetIndex d) (ω : BrownianSheetIndex d → ℝ) :
    brownianSheetCoordinateProcess d t ω = ω t := sorry

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Exercise 21.5.4: a Brownian sheet on `[0,1]^d` is a Gaussian process with covariance kernel
`∏ᵢ min (sᵢ, tᵢ)` that admits an almost surely continuous modification. -/
class IsBrownianSheet (d : ℕ) (μ : Measure Ω) (W : BrownianSheetIndex d → Ω → ℝ) : Prop
    extends IsGaussianProcess W μ where
  /-- The covariance kernel of a Brownian sheet is `∏ᵢ min (sᵢ, tᵢ)`. -/
  covariance_eq :
    ∀ s t : BrownianSheetIndex d, cov[W s, W t; μ] = brownianSheetCovariance s t
  /-- A Brownian sheet admits a modification with almost surely continuous sample paths. -/
  exists_continuous_modification :
    ∃ W' : BrownianSheetIndex d → Ω → ℝ,
      AreModifications μ W W' ∧ HasAlmostSurelyContinuousPaths μ W'

/-- A Gaussian process with Brownian-sheet covariance and almost surely continuous paths is a
Brownian sheet. -/
instance {d : ℕ} {μ : Measure Ω} {W : BrownianSheetIndex d → Ω → ℝ}
    (hgauss : IsGaussianProcess W μ)
    (hcov : ∀ s t : BrownianSheetIndex d, cov[W s, W t; μ] = brownianSheetCovariance s t)
    (hcont : HasAlmostSurelyContinuousPaths μ W) :
    IsBrownianSheet d μ W := sorry

-- Proof sketch: realize the coordinate process on path space under a Gaussian probability law
-- whose finite-dimensional marginals have covariance matrix
-- `(brownianSheetCovariance s t)_{s,t}`, obtained from a suitable orthonormal basis on
-- `[0,1]^d`.
/-- Part (1): there exists a Gaussian process on `[0,1]^d` whose covariance kernel is
`∏ᵢ min (sᵢ, tᵢ)`. -/
theorem exists_brownianSheetGaussianProcess (d : ℕ) :
    ∃ μ : ProbabilityMeasure (BrownianSheetIndex d → ℝ),
      IsGaussianProcess (brownianSheetCoordinateProcess d) (μ : Measure (BrownianSheetIndex d → ℝ)) ∧
      ∀ s t : BrownianSheetIndex d,
        cov[brownianSheetCoordinateProcess d s, brownianSheetCoordinateProcess d t;
          (μ : Measure (BrownianSheetIndex d → ℝ))] = brownianSheetCovariance s t := sorry

-- Proof sketch: apply the continuity criterion from Remark 21.7 to the Gaussian process from
-- part (1), using the Brownian-sheet covariance kernel to obtain the required moment bounds, and
-- then package the Gaussian, covariance, and path-regularity clauses into `IsBrownianSheet`.
/-- Part (2): the Brownian-sheet coordinate process on `[0,1]^d` carries a Brownian-sheet law on
path space. -/
theorem exists_brownianSheetContinuousModification (d : ℕ) :
    ∃ μ : ProbabilityMeasure (BrownianSheetIndex d → ℝ),
      IsBrownianSheet d (μ : Measure (BrownianSheetIndex d → ℝ))
        (brownianSheetCoordinateProcess d) := sorry

end ProbabilityTheory
