import Mathlib
import Nesterov.Chap07.Definition_7_27

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Lemma 7.6 lies in the Chapter 7 finite-family ellipsoid-rounding domain.

Sampled owner-style declarations:
- `affineEllipsoid` in `Chap03/Lemma_3_2_7`, the chapter owner of the unit ellipsoid;
- `matrixEllipsoid` in `Chap07/Definition_7_26`, the source-facing owner of radius-parametrized
  ellipsoids;
- `IsBetaRounding` in `Chap07/Definition_7_27`, the chapter owner for the pair of inner/outer
  ellipsoid containments;
- `weightedPrimalAverage` in `Chap07/Proposition_7_30`, a nearby Chapter 7 mean construction for
  finite families.

Best owner abstraction:
- source-facing: Lemma 7.6's empirical ellipsoid rounding of `convexHull ℝ (Set.range a)`;
- core/canonical: `IsBetaRounding` together with the underlying ellipsoid owners
  `affineEllipsoid` and `matrixEllipsoid`;
- bridge/view: the explicit arithmetic-mean and empirical-matrix formulas below.

Primitive data:
- the vertex family `a : Fin m → E`.

Derived API:
- the arithmetic mean of the vertices;
- the radius `√(m (m - 1))`;
- the normalized empirical shape matrix;
- the resulting `IsBetaRounding` witness for the convex hull.

The main duplicate wheel in the previous version was the conjunction-shaped theorem statement:
its two conclusions are exactly the fields of `IsBetaRounding`. This file now states the result at
that owner level and keeps the coordinate formulas only as supporting definitions.
-/

/-- The arithmetic mean of the vertices `a i`. -/
def polytopeArithmeticMean (a : Fin m → E) : E :=
  (m : ℝ)⁻¹ • ∑ i : Fin m, a i

/-- The outer-radius parameter `R = √(m (m - 1))` used in the empirical ellipsoid bound. -/
def polytopeRoundingRadius (m : ℕ) : ℝ :=
  Real.sqrt ((m : ℝ) * (m - 1 : ℕ))

/-- The empirical covariance-shape matrix
`R⁻² ∑ᵢ (aᵢ - â) (aᵢ - â)ᵀ` attached to the vertex family `a`. -/
def polytopeRoundingMatrix (a : Fin m → E) : Matrix (Fin n) (Fin n) ℝ :=
  ((polytopeRoundingRadius m) ^ (2 : ℕ))⁻¹ •
    ∑ i : Fin m,
      Matrix.vecMulVec
        (a i - polytopeArithmeticMean a)
        (a i - polytopeArithmeticMean a)

-- Proof sketch: compare support functions. For the outer inclusion, compute the support function of
-- the ellipsoid with shape `polytopeRoundingMatrix a` and bound it below by the maximum over the
-- vertices. For the inner inclusion, use the zero-sum relation among the centered support values
-- and optimize their squared sum under the upper bound by the maximal component.
/-- Lemma 7.6: if the convex hull of the vertices `a i` has nonempty interior, then the empirical
ellipsoid centered at the arithmetic mean gives a
`polytopeRoundingRadius m`-rounding of that convex hull. -/
theorem convexHull_range_between_empirical_ellipsoids_of_interior_nonempty
    (a : Fin m → E)
    (hinterior : (interior (convexHull ℝ (Set.range a))).Nonempty) :
    IsBetaRounding
      (convexHull ℝ (Set.range a))
      (polytopeRoundingRadius m)
      (polytopeRoundingMatrix a)
      (polytopeArithmeticMean a) := sorry

end
