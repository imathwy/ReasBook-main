import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 4.3 is `source-facing`: it identifies the conjugate of the support function with
the indicator of the closed convex hull. The owner abstractions already live upstream:
`extendedIndicator` in Chapter 2, `support_function` in Chapter 2, and Definition 4.1's owner
pair `conjugate_function` / `conjugate_function_primal`. This file therefore keeps only the
proposition itself. -/
recall conjugate_function_primal

-- Proof sketch: identify the textbook support function on `E` with the chapter owner
-- `x ↦ support_function C (InnerProductSpace.toDualMap ℝ E x)`, then apply the primal-side
-- conjugate surface `f∗`. Combine Proposition 4.1 with the
-- biconjugate identity for proper closed convex functions and the support-function invariance under
-- closure and convex hull.
/-- Proposition 4.3: after identifying the Euclidean pairing with the canonical dual pairing via
`InnerProductSpace.toDualMap`, the conjugate of the support function `σ_C` is the indicator
function `δ_cl(conv(C))`. The textbook assumes `C` is nonempty, but the same equality still holds
for `C = ∅`, since both sides are then constantly `⊤`. -/
theorem conjugate_function_support_function_eq_extendedIndicator_closure_convexHull (C : Set E) :
    ((fun z ↦ support_function C (InnerProductSpace.toDualMap ℝ E z))∗) =
      extendedIndicator (closure (convexHull ℝ C)) := sorry

end
