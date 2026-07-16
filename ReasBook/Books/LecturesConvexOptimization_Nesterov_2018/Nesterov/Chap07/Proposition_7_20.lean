import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_1_5
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_35
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_43

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace (nonnegativeOrthant)
open scoped SymmetricBox WithTopConvexAnalysis

variable {n : ℕ} {m : ℕ+}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.20 lies in the Chapter 7 weighted max-absolute-coordinate / subdifferential
domain.

Sampled owner-style declarations:
- `IsSubgradientAt`, `subdifferential`, and the notation `∂ f(x)` in
  `Chap03/Definition_3_1_5`, the chapter owners for subgradients;
- `symmetricBox`, the notation `B(g)`, and `signSymmetricConvexHull` in
  `Chap07/Definition_7_35`, the chapter owners for the boxes `B(a)` and their convex hull;
- `maxWeightedAbsoluteCoordinateSum` and the orthant bridge
  `maxWeightedAbsoluteCoordinateSumOfOrthant` in `Chap07/Definition_7_43`, the Chapter 7 owner
  surface for the objective `x ↦ maxᵢ ∑ⱼ aᵢⱼ |xⱼ|`.

Best owner abstraction:
- source-facing: Proposition 7.20 itself, stated for `maxWeightedAbsoluteCoordinateSum`;
- core/canonical: the Chapter 3 owner subdifferential `∂`;
- bridge/view: the Chapter 7 box notation `B(a)` and the hull owner
  `signSymmetricConvexHull`.

Primitive data:
- a positive number of branches `m`;
- a family `a : Fin (m : ℕ) → E` in the nonnegative orthant.

Derived API:
- the origin-subdifferential identity below.

This refinement deletes the duplicate local real-valued subgradient/subdifferential and box
wrappers. The proposition is now stated directly through the existing chapter owners `∂`,
`signSymmetricConvexHull`, and the orthant bridge to `maxWeightedAbsoluteCoordinateSum`, while
keeping the same mathematical content as the textbook statement.
-/

-- Proof sketch: for each index `i`, compute `∂fᵢ(0)` for `fᵢ(x) = ∑ⱼ aᵢⱼ |xⱼ|` as the box
-- `B(a i)` by checking the subgradient inequality coordinate-wise. Since all
-- `fᵢ(0) = 0`, every branch is active in the pointwise maximum at the origin, and the standard
-- subdifferential formula for a finite maximum gives the convex hull of the union of these boxes.
/-- Proposition 7.20: if `a₁, …, aₘ ∈ ℝⁿ₊` and
`hat f(x) = maxᵢ ∑ⱼ aᵢⱼ |xⱼ|`, then `∂ hat f(0)` is the sign-symmetric convex hull
`Conv (⋃ i, B(aᵢ))`. -/
theorem subdifferential_zero_maxWeightedAbsoluteCoordinateSum_eq_signSymmetricConvexHull
    {a : Fin (m : ℕ) → E} (ha : ∀ i : Fin (m : ℕ), a i ∈ nonnegativeOrthant n) :
    ∂ (fun x : E ↦
        (maxWeightedAbsoluteCoordinateSumOfOrthant a ha x : WithTop ℝ))(0) =
      signSymmetricConvexHull a := sorry
