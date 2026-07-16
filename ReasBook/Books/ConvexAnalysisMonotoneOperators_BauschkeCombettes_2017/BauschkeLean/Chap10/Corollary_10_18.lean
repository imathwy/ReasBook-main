import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.BauschkeLean.Chap09.Example_9_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.BauschkeLean.Chap10.Proposition_10_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open ERealFunction

-- Proof sketch: strict convexity on `Set.univ` gives continuity via
-- `ConvexOn.locallyLipschitz`, finite dimensionality upgrades bounded closed subsets to compact
-- ones, and Proposition 10.17 then supplies a modulus positive away from `0` on `C`.
/-- Corollary 10.18: on a finite-dimensional real normed space, every strictly convex real-valued
function is uniformly convex on each bounded closed convex subset. -/
theorem uniformConvexOn_of_finiteDimensional_of_strictConvexOn_univ
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (f : H → ℝ) (hstrict : StrictConvexOn ℝ Set.univ f)
    (C : Set H) (hC_bounded : Bornology.IsBounded C)
    (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) :
    ∃ ψ : ℝ → ℝ, (∀ ⦃r : ℝ⦄, r ≠ 0 → 0 < ψ r) ∧ UniformConvexOn C ψ f := by
  have hstrictC : StrictConvexOn ℝ C f := hstrict.subset (by simp) hC_convex
  have hconv : ConvexOn ℝ Set.univ f := hstrict.convexOn
  have hloc : LocallyLipschitz f := hconv.locallyLipschitz
  have hcont : Continuous f := hloc.continuous
  have hC_compact : IsCompact C :=
    hC_bounded.isCompact_closure.of_isClosed_subset hC_closed subset_closure
  exact exists_uniformConvexOn_of_isCompact_of_strictConvexOn_of_continuousOn
    f C hC_compact hstrictC hcont.continuousOn
