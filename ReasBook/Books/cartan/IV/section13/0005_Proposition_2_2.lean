import cartan.IV.section13.«0003_Definition_IV_1_extra_3»
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling:
* primary domain: convergence-domain statements for two-variable formal power series
* source-facing owners reused here: `formalSeriesConvergenceLocus` and
  `formalSeriesConvergenceDomain`
* core/canonical owner abstraction in this chapter: the convergence locus/domain from
  `0003_Definition_IV_1_extra_3`, whose primitive datum is weighted norm summability
* nearby owner-pattern samples checked before refining:
  `mem_formalSeriesConvergenceLocus_iff`,
  `mem_formalSeriesConvergenceDomain_iff`,
  `formalSeriesConvergenceLocus_of_bounded_coefficients`,
  `FormalMultilinearSeries.summable_norm_mul_pow`

This file stays at the source-facing theorem layer. The first two results only use the chapter
convergence-domain owners, while the last two additionally need the ring structure coming from the
actual series terms `a p q * z₁^p * z₂^q`.
-/

universe u

section ConvergenceDomain

variable {𝕜 : Type u} [SeminormedAddCommGroup 𝕜]

/-- Proposition 2.2 (1): if `(r₁, r₂)` belongs to the domain of convergence, then the radii
defining the closed polydisc are nonnegative. -/
theorem nonneg_radii_of_mem_formal_series_convergence_domain
    (a : ℕ → ℕ → 𝕜) {r₁ r₂ : ℝ}
    (hr : (r₁, r₂) ∈ formalSeriesConvergenceDomain a) :
    0 ≤ r₁ ∧ 0 ≤ r₂ := sorry

/-- Proposition 2.2 (2): if `(r₁, r₂)` belongs to the domain of convergence, then the normal
majorant series `∑ ‖a p q‖ r₁^p r₂^q` is summable. -/
theorem summable_double_power_series_normal_majorant_of_mem_domain
    (a : ℕ → ℕ → 𝕜) {r₁ r₂ : ℝ}
    (hr : (r₁, r₂) ∈ formalSeriesConvergenceDomain a) :
    Summable (fun n : ℕ × ℕ ↦ ‖a n.1 n.2‖ * r₁ ^ n.1 * r₂ ^ n.2) := sorry

end ConvergenceDomain

section SeriesTerms

variable {𝕜 : Type u} [NormedRing 𝕜]

/-- Proposition 2.2 (3): if `(r₁, r₂)` belongs to the domain of convergence, then on the closed
polydisc `‖z₁‖ ≤ r₁`, `‖z₂‖ ≤ r₂` each term of the double power series is dominated by the
normal majorant term `‖a p q‖ r₁^p r₂^q`. -/
theorem norm_double_power_series_term_le_normal_majorant_of_mem_domain
    (a : ℕ → ℕ → 𝕜) {r₁ r₂ : ℝ}
    (hr : (r₁, r₂) ∈ formalSeriesConvergenceDomain a)
    (n : ℕ × ℕ) (z₁ z₂ : 𝕜) (hz₁ : ‖z₁‖ ≤ r₁) (hz₂ : ‖z₂‖ ≤ r₂) :
    ‖a n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2‖ ≤ ‖a n.1 n.2‖ * r₁ ^ n.1 * r₂ ^ n.2 := sorry

/-- Proposition 2.2 (4): if `(‖z₁‖, ‖z₂‖)` does not belong to the closure of `Γ`, then the
double series `∑ a p q z₁^p z₂^q` is divergent at `(z₁, z₂)`. -/
theorem not_summable_double_power_series_of_norm_pair_not_mem_closure
    (a : ℕ → ℕ → 𝕜) {z₁ z₂ : 𝕜}
    (hz : (‖z₁‖, ‖z₂‖) ∉ closure (formalSeriesConvergenceLocus a)) :
    ¬ Summable (fun n : ℕ × ℕ ↦ a n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2) := sorry

end SeriesTerms
