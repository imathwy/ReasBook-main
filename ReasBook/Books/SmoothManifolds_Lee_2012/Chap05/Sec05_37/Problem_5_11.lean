import Mathlib
import SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifoldsLee.Chap05.Sec05_35.Definition_5_35_extra_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff
open Manifold

noncomputable section

local notation "Plane" => ℝ × ℝ

/-- Problem 5-11 (1): Part (a) for `Φ(x,y)=x^2-y^2`; its zero set is not an embedded curve in
`ℝ²`. -/
-- Proof sketch: identify the zero set with the two diagonals meeting transversely at the origin
-- and show the induced topology is not locally interval-like there.
theorem quadraticDifferenceZeroSet_not_embedded_curve :
    ¬ ({p : Plane | p.1 ^ 2 - p.2 ^ 2 = 0} : Set Plane).AdmitsEmbeddedCurveStructure := sorry

/-- Problem 5-11 (2): Part (b) for `Φ(x,y)=x^2-y^2`; under the project owner predicate on the
existing subtype, the transverse crossing does not admit an immersed curve structure. -/
-- Proof sketch: the subtype has a single origin point where two diagonal branches cross. A
-- one-dimensional immersion is locally an embedding at each source point, so it cannot model four
-- local branches through one source point.
theorem quadraticDifferenceZeroSet_no_immersed_curve_structure :
    ¬ ({p : Plane | p.1 ^ 2 - p.2 ^ 2 = 0} : Set Plane).AdmitsImmersedCurveStructure := sorry

/-- Problem 5-11 (3): Part (c) for `Ψ(x,y)=x^2-y^3`; its zero set is not an embedded curve in
`ℝ²`. -/
-- Proof sketch: analyze the cusp at the origin and show that the subset topology cannot make the
-- zero set into a smooth embedded `1`-manifold of the plane.
theorem cuspPolynomialZeroSet_not_embedded_curve :
    ¬ ({p : Plane | p.1 ^ 2 - p.2 ^ 3 = 0} : Set Plane).AdmitsEmbeddedCurveStructure := sorry

/-- Problem 5-11 (4): Part (c) for `Ψ(x,y)=x^2-y^3`; its zero set admits no topology and smooth
structure making its inclusion into `ℝ²` an immersed curve. -/
-- Proof sketch: any such structure would yield a smooth immersed parametrization of the cusp, but
-- every parametrization through the singular point has vanishing derivative there.
theorem cuspPolynomialZeroSet_no_immersed_curve_structure :
    ¬ ({p : Plane | p.1 ^ 2 - p.2 ^ 3 = 0} : Set Plane).AdmitsImmersedCurveStructure := sorry
