import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling note: this item lives in one-variable complex analysis on oriented boundaries.
-- The source-facing boundary owner is `IsOrientedBoundaryOf`; the holomorphy owner for
-- neighborhood-of-`K` hypotheses is Mathlib's canonical `AnalyticOnNhd`; the bridge/view
-- ingredient is `Path.closedPathIndex_add_eq_of_abs_lt` from Proposition 8.3; and the
-- core/canonical zero-count owner is `MeromorphicOn.divisor`, already used by the chapter
-- argument principle. The theorem below therefore stays a direct divisor-sum statement, with no
-- parallel local zero-count wrapper and no auxiliary open-set witness in the public API.

open MeromorphicOn

noncomputable section

universe u

/-- Exercise 19: Rouché's theorem on an oriented boundary. If `f` and `g` are holomorphic on a
neighborhood of `K`, if `Γ` is the oriented boundary of `K`, and if `‖g z‖ < ‖f z‖` for every
boundary point `z ∈ frontier K`, then `f + g` and `f` have the same total divisor sum on `K`;
equivalently, they have the same number of zeros in `K` counted with multiplicity. -/
theorem rouche_theorem_on_oriented_boundary
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ) {f g : ℂ → ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ)
    (hf : AnalyticOnNhd ℂ f K)
    (hg : AnalyticOnNhd ℂ g K)
    (hboundary : ∀ z ∈ frontier K, ‖g z‖ < ‖f z‖) :
    ∑ᶠ z, divisor (f + g) K z = ∑ᶠ z, divisor f K z := sorry
