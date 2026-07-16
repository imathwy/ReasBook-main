import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_4_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 1.4.4 lies in the finite-dimensional Euclidean inner-product-space domain.

Relevant owner-style declarations sampled before refining:
* `inner ℝ`, the canonical inner product on `E`
* `(fun x : E ↦ ‖x‖)`, the inherited norm on `E`
* mathlib `EuclideanSpace.inner_eq_star_dotProduct`, the canonical coordinate bridge for the
  Euclidean inner product
* mathlib `EuclideanSpace.norm_eq`, the canonical sum-of-squares norm formula

Best owner abstraction:
* the canonical `InnerProductSpace` and `Norm` structure on `EuclideanSpace ℝ (Fin n)`

Primitive data:
* vectors `x y : E`

Derived API:
* `EuclideanSpace.inner_eq_star_dotProduct`, the coordinate formula for the Euclidean inner product
* `EuclideanSpace.norm_eq`, the coordinate formula for the Euclidean norm
* the real-specialized textbook rewrites below, where absolute values disappear and the dot
  product may be read in the usual order

Source/core/bridge triage:
* source-facing: the Euclidean inner product and norm on `ℝⁿ`
* core/canonical: `inner ℝ` and `‖·‖` on `EuclideanSpace ℝ (Fin n)`
* bridge/view: `EuclideanSpace.inner_eq_star_dotProduct` and `EuclideanSpace.norm_eq`

The canonical owner operations come from the `InnerProductSpace` and `Norm` structures on `E`,
and the coordinate bridges are the upstream mathlib `EuclideanSpace` theorems already recalled in
the chapter file. This item therefore reuses those owners directly instead of keeping parallel
local copies or the unnecessary `EuclideanSpace.equiv` transport layer. -/

/- Definition 1.4.4: the Euclidean inner product on `ℝⁿ` is the inherited inner product. -/
#check (inner ℝ : E → E → ℝ)

/- The Euclidean norm on `ℝⁿ` is the inherited norm. -/
#check (norm : E → ℝ)

/- In coordinates, the Euclidean inner product is the standard dot product. -/
#check
  (EuclideanSpace.inner_eq_star_dotProduct :
    ∀ x y : E, inner ℝ x y = y ⬝ᵥ x)

/- Over `ℝ`, the coordinate formula can be read in the textbook order `xᵀ y`. -/
#check
  (show ∀ x y : E, inner ℝ x y = x ⬝ᵥ y from
    fun x y ↦ by
      simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct x y))

/- The Euclidean norm is the square root of the sum of the squares of the coordinates. -/
#check
  (EuclideanSpace.norm_eq :
    ∀ x : E, ‖x‖ = Real.sqrt (∑ i, ‖x i‖ ^ 2))

/- Over `ℝ`, the norm formula is the textbook square-root-of-sum-of-squares identity. -/
#check
  (show ∀ x : E, ‖x‖ = Real.sqrt (∑ i, (x i) ^ 2) from
    fun x ↦ by
      simpa using (EuclideanSpace.norm_eq x))
