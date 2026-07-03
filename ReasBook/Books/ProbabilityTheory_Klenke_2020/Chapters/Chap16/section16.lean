import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_16_16 (from Items/Chap16) -/
open MeasureTheory ProbabilityTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- The primitive data of a real Lévy--Khintchine triple: Gaussian coefficient, drift, and Lévy
measure. -/
structure LevyKhinchinTriple where
  sigma2 : ℝ
  b : ℝ
  ν : Measure ℝ

/-- Definition 16.16 (1): a canonical measure on `ℝ` has no atom at `0` and finite integral of
`x ↦ min (x^2, 1)`; for Lévy measures on `ℝ`, these side conditions already imply
σ-finiteness. -/
class IsCanonicalMeasure (ν : Measure ℝ) : Prop where
  measure_singleton_zero : ν ({0} : Set ℝ) = 0
  integrable_sq_min_one : Integrable (fun x : ℝ ↦ min (x ^ (2 : ℕ)) 1) ν

namespace IsCanonicalMeasure

/-- For a canonical measure on `ℝ`, σ-finiteness is a derived consequence of the no-atom and
truncated-second-moment conditions. -/
theorem sigmaFinite {ν : Measure ℝ} (hν : IsCanonicalMeasure ν) : SigmaFinite ν := sorry

instance (ν : Measure ℝ) [hν : IsCanonicalMeasure ν] : SigmaFinite ν :=
  hν.sigmaFinite

end IsCanonicalMeasure

/-- The zero measure on `ℝ` is canonical. -/
instance : IsCanonicalMeasure (0 : Measure ℝ) := sorry

/-- Definition 16.16 (2): a canonical triple `(σ², b, ν)` consists of a nonnegative Gaussian
coefficient, an arbitrary drift term, and a canonical measure on `ℝ`. -/
class IsCanonicalTriple (τ : LevyKhinchinTriple) : Prop where
  sigma2_nonneg : 0 ≤ τ.sigma2
  isCanonicalMeasure : IsCanonicalMeasure τ.ν

attribute [instance] IsCanonicalTriple.isCanonicalMeasure

/-- Any triple with zero Gaussian coefficient and zero jump measure is canonical. -/
instance (b : ℝ) : IsCanonicalTriple { sigma2 := 0, b := b, ν := 0 } := sorry

end MeasureTheory.ProbabilityMeasure
