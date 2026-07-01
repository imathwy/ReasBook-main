import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: the estimate `‖v k - xStar‖² ≤ 2 * D` gives a uniform closed ball centered
-- at `xStar` containing every `v k`. Since each `x k` and `y k` lies in the convex hull of the
-- finite prefix `v 0, ..., v k`, convexity of that closed ball implies the same uniform bound for
-- `x k` and `y k`. Therefore the union of the three ranges is bounded.
/-- Core owner form: if `v` has bounded range and each `x_k` and `y_k` lies in the convex hull of
the finite prefix `v_0, ..., v_k`, then the union of the three ranges is bounded. -/
theorem bounded_union_of_prefix_convex_hull_sequences_of_isBounded
    (v x y : ℕ → E)
    (hx : ∀ k, x k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)))
    (hy : ∀ k, y k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)))
    (hv : Bornology.IsBounded (Set.range v)) :
    Bornology.IsBounded (Set.range v ∪ Set.range x ∪ Set.range y) := sorry

/-- The pointwise squared-distance estimate `‖v_k - xStar‖² ≤ 2 D` places the full range of `v`
in a common closed ball, hence `Set.range v` is bounded. -/
theorem isBounded_range_of_sqDist_le
    (xStar : E) (D : ℝ) (v : ℕ → E)
    (hv : ∀ k, ‖v k - xStar‖ ^ 2 ≤ 2 * D) :
    Bornology.IsBounded (Set.range v) := sorry

/-- Proposition 6.8: if each `x_k` and `y_k` lies in the convex hull of the finite prefix
`v_0, ..., v_k` and the points `v_k` satisfy `‖v_k - xStar‖² ≤ 2 D` for all `k ≥ 0`, then
the three sequences are bounded, equivalently the union of their ranges is bounded. Here `D`
is the scalar value corresponding to the source quantity `d(xStar)`. -/
theorem bounded_union_of_prefix_convex_hull_sequences
    (xStar : E) (D : ℝ) (v x y : ℕ → E)
    (hx : ∀ k, x k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)))
    (hy : ∀ k, y k ∈ convexHull ℝ (Set.range (fun i : Fin (k + 1) ↦ v i)))
    (hv : ∀ k, ‖v k - xStar‖ ^ 2 ≤ 2 * D) :
    Bornology.IsBounded (Set.range v ∪ Set.range x ∪ Set.range y) := sorry
