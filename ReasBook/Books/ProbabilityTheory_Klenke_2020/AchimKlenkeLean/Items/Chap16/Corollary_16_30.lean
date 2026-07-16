import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Theorem_16_29

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

variable {ν : ProbabilityMeasure ℝ} {α β : ℝ}

-- Proof sketch: apply Theorem 16.29 to obtain the regularly varying tail of order `-α` for the
-- law `ν`, then use the standard tail-integrability criterion to deduce finiteness of the
-- `β`th absolute moment whenever `0 < β < α`.
/-- Corollary 16.30 (1): if a real probability law lies in the domain of attraction of a stable
distribution with index `α`, then every absolute moment of order `β ∈ (0, α)` is finite. -/
theorem IsInDomainOfAttractionOfStableWithIndex.integrable_abs_rpow
    (hν : ν.IsInDomainOfAttractionOfStableWithIndex α)
    (hβ₀ : 0 < β) (hβα : β < α) :
    Integrable (fun x : ℝ ↦ |x| ^ β) (ν : Measure ℝ) := sorry

-- Proof sketch: use Theorem 16.29 to identify the power-law tail with exponent `-α`; when
-- `α < 2` and `β > α`, the tail-integral test shows that the `β`th absolute moment diverges.
/-- Corollary 16.30 (2): if a real probability law lies in the domain of attraction of a stable
distribution with index `α < 2`, then every absolute moment of order `β > α` is infinite. -/
theorem IsInDomainOfAttractionOfStableWithIndex.lintegral_abs_rpow_eq_top
    (hν : ν.IsInDomainOfAttractionOfStableWithIndex α)
    (hα₂ : α < 2) (hαβ : α < β) :
    ∫⁻ x, ENNReal.ofReal (|x| ^ β) ∂(ν : Measure ℝ) = ⊤ := sorry

end MeasureTheory.ProbabilityMeasure
