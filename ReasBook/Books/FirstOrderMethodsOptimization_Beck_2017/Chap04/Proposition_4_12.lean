import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (b y : E) (c : ℝ)

/- Proposition 4.12 is `source-facing`: its primitive data are the quadratic coefficients `A`, `b`,
and `c`, and its main content is the explicit maximizer/value of the quadratic Fenchel objective on
`ℝ^n`. The `core/canonical` owner abstraction for the conjugate itself is already Chapter 4's
`conjugate_function`, so this file should reuse that owner rather than restating the same supremum
formula locally. -/

-- Proof sketch: complete the square in
-- `x ↦ dotProduct y x - ((1 / 2) * dotProduct x (A.mulVec x) + dotProduct b x + c)` to rewrite it
-- as a negative definite quadratic centered at `A⁻¹.mulVec (y - b)` plus a constant. Since `hA`
-- implies `A` is positive definite, the centered quadratic term is nonpositive and vanishes
-- exactly at `x = A⁻¹.mulVec (y - b)`, yielding the greatest value at that point.
/-- Proposition 4.12: for
`f(x) = (1 / 2) xᵀ A x + bᵀ x + c` with `A ∈ 𝕊_{++}^n`, the maximum in the defining Fenchel
objective is attained at `x = A⁻¹ (y - b)`. -/
theorem strictly_convex_quadratic_conjugate_isGreatest
    :
    IsGreatest
      (Set.range fun x : E ↦
        dotProduct y x -
          ((1 / 2 : ℝ) * dotProduct x (A.mulVec x) + dotProduct b x + c))
      (dotProduct y (A⁻¹.mulVec (y - b)) -
        ((1 / 2 : ℝ) * dotProduct (A⁻¹.mulVec (y - b)) (A.mulVec (A⁻¹.mulVec (y - b))) +
          dotProduct b (A⁻¹.mulVec (y - b)) + c)) := sorry

-- Proof sketch: use `strictly_convex_quadratic_conjugate_isGreatest` to identify the supremum in
-- `conjugate_function` with the value of the quadratic objective at
-- `x = A⁻¹.mulVec (y - b)`. Then expand that value and simplify the completed-square expression to
-- obtain `(1 / 2) * dotProduct (y - b) (A⁻¹.mulVec (y - b)) - c`.
/-- The conjugate of the positive-definite quadratic
`x ↦ (1 / 2) xᵀ A x + bᵀ x + c`, evaluated on `ℝ^n` through the Euclidean duality map, is
`y ↦ (1 / 2) (y - b)ᵀ A⁻¹ (y - b) - c`. -/
theorem strictly_convex_quadratic_conjugate_eq
    :
    conjugate_function
        (fun x : E ↦
          (((1 / 2 : ℝ) * dotProduct x (A.mulVec x) + dotProduct b x + c : ℝ) : EReal))
        (InnerProductSpace.toDualMap ℝ E y) =
      (((1 / 2 : ℝ) * dotProduct (y - b) (A⁻¹.mulVec (y - b)) - c : ℝ) : EReal) := sorry

end
