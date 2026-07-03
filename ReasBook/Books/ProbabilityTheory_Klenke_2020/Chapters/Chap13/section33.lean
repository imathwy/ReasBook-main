import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_13_33 (from Items/Chap13) -/
open Filter Set
open scoped Topology

section

-- Proof sketch: use a diagonal extraction on the rational numbers to obtain pointwise convergence
-- along a subsequence on `ℚ`, define the candidate limit by the right-envelope of those rational
-- limits, and use monotonicity plus right continuity to upgrade convergence to every continuity
-- point of the limit function.
/-- Theorem 13.33: every uniformly bounded sequence in Helly's class `V` admits a subsequence
that converges pointwise at every continuity point of a limit function in the same class. -/
theorem exists_helly_subsequence_tendsto_at_continuity_points
    (u : ℕ → StieltjesFunction ℝ)
    (h_uniform : Bornology.IsBounded (⋃ n, range (u n))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ F : StieltjesFunction ℝ, Bornology.IsBounded (range F) ∧
        ∀ ⦃x : ℝ⦄, ContinuousAt F x →
          Tendsto (fun k ↦ u (φ k) x) atTop (𝓝 (F x)) := sorry

end
