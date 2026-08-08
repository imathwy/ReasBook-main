import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_14
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_20
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_17
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_21

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise
open InnerProductSpace
open Metric

/- Proposition 3.32 is a `source-facing` computation for the owner objective
`fermatWeberObjective`. The `core/canonical` owner is the chapter extendedRealSubdifferential
`subdifferentialAt`, and the Euclidean bridge/view owner is `euclideanSubdifferentialAt`. The
supporting declarations are the finite-sum rule
`subdifferentialAt_finset_sum_eq_sum_subdifferentialAt`, the affine Euclidean-norm formula
`euclidean_subdifferentialAt_affine_l2_norm_eq_piecewise`, and the scalar-composition rule
`subdifferentialAt_comp_eq_smul_subdifferentialAt`. The weighted single-site distance term is
therefore only a derived view, not a second public owner abstraction. -/

section

variable {m d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

recall fermatWeberObjective
recall euclideanSubdifferentialAt
recall euclidean_subdifferentialAt_affine_l2_norm_eq_piecewise
recall subdifferentialAt_comp_eq_smul_subdifferentialAt
recall subdifferentialAt_finset_sum_eq_sum_subdifferentialAt

-- Proof sketch: rewrite the weighted one-site distance `y ↦ ω * dist y a` using `dist_eq_norm`
-- into `y ↦ ω * ‖y - a‖`, then obtain its Euclidean
-- extendedRealSubdifferential from the affine `ℓ₂` formula and the scalar-composition rule for the
-- nonnegative factor `ω`.
private theorem euclidean_subdifferentialAt_weighted_dist_eq_piecewise
    (ω : ℝ) (hω : 0 ≤ ω) (a x : E) :
    euclideanSubdifferentialAt (fun y : E ↦ ω * dist y a) x =
      if x = a then
        closedBall (0 : E) ω
      else
        {ω • ((‖x - a‖)⁻¹ • (x - a))} := by
  sorry

-- Proof sketch: rewrite `fermatWeberObjective ω a` as the finite sum of the weighted one-site
-- terms `fun y ↦ ω i * dist y (a i)` using `fermatWeberObjective_apply`. Apply the owner
-- finite-sum rule for subdifferentials, then transport each summand through the private
-- one-site bridge above.
/-- Proposition 3.32: the vector-side extendedRealSubdifferential of the Fermat-Weber objective
`x ↦ ∑ i, ω_i ‖x - a_i‖₂` is the finite Minkowski sum of the single-term subdifferentials, so each
summand contributes the normalized vector `ω_i (x - a_i) / ‖x - a_i‖₂` away from its site and the
closed Euclidean ball of radius `ω_i` at its site; this remains valid for nonnegative weights,
with `ω_i = 0` giving the singleton `{0}` in both cases. -/
theorem euclidean_subdifferentialAt_fermatWeberObjective_eq_finset_sum_piecewise
    (ω : Fin m → ℝ) (hω : ∀ i, 0 ≤ ω i) (a : Fin m → E) (x : E) :
    euclideanSubdifferentialAt (fermatWeberObjective ω a) x =
      ∑ i : Fin m,
        if x = a i then
          closedBall (0 : E) (ω i)
        else
          {ω i • ((‖x - a i‖)⁻¹ • (x - a i))} := sorry

end
