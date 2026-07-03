import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_6 (from Chap03) -/
open scoped BigOperators Pointwise

universe u v

variable {ι : Type u} {E : Type v} [AddCommGroup E] [Module ℝ E]

/- Proposition 3.6 (1): the finite Minkowski sum of a family of convex subsets is convex,
canonically formalized by `convex_sum`. -/
recall convex_sum

/-- Proposition 3.6 (2): a finite weighted Minkowski sum of convex subsets of a real vector space
is convex. -/
theorem convex_weighted_minkowski_sum_finset
    (s : Finset ι) (α : ι → ℝ) (C : ι → Set E) (hC : ∀ i ∈ s, Convex ℝ (C i)) :
    Convex ℝ (∑ i ∈ s, α i • C i) := by
  exact convex_sum (fun i ↦ α i • C i) fun i hi ↦ (hC i hi).smul (α i)
