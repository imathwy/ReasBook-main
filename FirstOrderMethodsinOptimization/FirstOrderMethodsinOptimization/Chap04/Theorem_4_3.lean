import FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

section

variable {p : ℕ}
variable {E : Fin p → Type u}
variable [∀ i, AddCommGroup (E i)]
variable [∀ i, Module ℝ (E i)]

/- Theorem 4.3 is a `bridge/view` item in convex conjugacy: its source-facing content is the
separable-sum conjugacy formula, while the product-dual map itself is already owned canonically by
mathlib's Pi linear-map API as `LinearMap.lsum`. The primitive data are the coordinate dual vectors
`y`; the product dual they determine is derived from that owner abstraction and should not be
duplicated locally. In the textbook, the `f i` are proper. For this `EReal` identity, the
essential part is that no coordinate function takes the value `⊥`; the nonempty-domain part of
properness is redundant here. -/

-- Proof sketch: unfold `conjugate_function` for the product-space sum and rewrite the pairing with
-- `LinearMap.lsum_apply`; evaluating the resulting sum of composed projections gives
-- `∑ i, y i (x i)`. The supremum then separates into independent coordinatewise suprema, which are
-- exactly the values of the individual conjugates.
/-- Theorem 4.3: if each coordinate function never takes the value `-∞`, then the conjugate of the
finite separable sum on the product space, evaluated at the canonical product dual
`LinearMap.lsum ℝ E ℝ y` determined by the coordinate dual vectors, is the sum of the
coordinatewise conjugates. -/
theorem conjugate_function_separable_sum_eq_sum_conjugate_function
    (f : ∀ i, E i → EReal) (h_ne_bot : ∀ i x, f i x ≠ ⊥) (y : ∀ i, Module.Dual ℝ (E i)) :
    conjugate_function (fun x : ∀ i, E i ↦ ∑ i, f i (x i)) (LinearMap.lsum ℝ E ℝ y) =
      ∑ i, conjugate_function (f i) (y i) := sorry

end
