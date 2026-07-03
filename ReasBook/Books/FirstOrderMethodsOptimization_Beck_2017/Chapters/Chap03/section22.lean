

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_22 (from Chap03) -/
universe u

section

open Metric
open InnerProductSpace (toDual)
open scoped RealInnerProductSpace

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)

local notation "P" => fun y ↦ (metricProjection C hC_nonempty hC_closed hC_convex y : E)

-- Proof sketch: if `x ∉ C`, use Proposition 3.12 to identify the gradient of
-- `y ↦ (infDist y C)^2 / 2` with `y - P_C(y)` and combine it with the singleton-subdifferential
-- criterion for differentiable convex functions to obtain the unique normalized subgradient vector.
-- If `x ∈ C`, rewrite the subgradient inequality for `y ↦ infDist y C` in Euclidean coordinates:
-- one inclusion follows by testing the inequality on points of `C` and on `x + v`, and the reverse
-- inclusion follows from the projection formula `infDist y C = ‖y - P_C(y)‖` together with the
-- normal-cone inequality and Cauchy-Schwarz.
/- Proposition 3.22 is a `bridge/view` theorem in the chapter subdifferential API: the owner
notion remains `subdifferentialAt`, and the left-hand side is stated through its canonical
Euclidean bridge `euclideanSubdifferentialAt`. The right-hand side still uses the owner
`normal_cone`, since the textbook formula is intrinsically the dual normal cone intersected with
the closed unit ball. -/
open Classical in
theorem euclidean_subdifferentialAt_infDist_eq_piecewise
    (x : E) :
    euclideanSubdifferentialAt (fun y ↦ infDist y C) x =
      if x ∈ C then
        {v : E | (toDual ℝ E v : Module.Dual ℝ E) ∈ normal_cone C x} ∩ closedBall (0 : E) 1
      else
        {((infDist x C)⁻¹ : ℝ) • (x - P x)} := sorry

end

/-! ### Theorem_3_22 (from Chap03) -/
universe u v

open scoped Topology

section

/-
Theorem 3.22 is `source-facing` at the Chapter 3 owner `subdifferential`. Domain sampling for the
max-rule API points to the following relevant declarations:

* `subdifferential` in `Definition_3_2` as the owner object.
* `directional_derivative_iSup_eq_iSup_active_indices` in `Theorem_3_9` for the canonical active
  index subtype of a finite pointwise supremum.
* `directional_derivative_eq_support_function_subdifferential_at_interior_point` in
  `Proposition_3_10` as the support-function bridge from directional derivatives to
  subdifferentials.
* `convexHull_iUnion_active_subdifferential_subset_subdifferential_iSup` in `Theorem_3_23` as the
  owner-level weak inclusion for the same active subdifferential family.

The primitive data here is only the ambient subdifferential of the supremum; the active-index
family is derived data and stays inline instead of being repackaged as a parallel public wrapper.
Those owner-level ingredients already live on the ambient finite-dimensional real normed-space
hypotheses, so no Euclidean structure belongs in the public statement here. As in the nearby
interior-point sum rules, membership `x ∈ ⋂ i, interior (effective_domain (f i))` already forces
each effective domain to be nonempty, so the public hypothesis only retains the genuinely used
no-`⊥` part.
-/
variable {E : Type u} {ι : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Finite ι] [Nonempty ι]

recall effective_domain
recall is_convex_function
recall subdifferential
recall convexHull_iUnion_active_subdifferential_subset_subdifferential_iSup

-- Proof sketch: combine the max-directional-derivative formula for the indexed supremum
-- `fun y ↦ ⨆ i, f i y` with the support-function description of subdifferentials at interior
-- points. The right-hand side is the convex hull of the union of the active subdifferentials over
-- the canonical active-index subtype, and equality of support functions of the two nonempty
-- compact convex sets then identifies the sets themselves.
/-- Theorem 3.22: max rule of subdifferential calculus. For a nonempty finite family of convex
functions that never attain `-∞`, the subdifferential of the pointwise supremum at an interior
point is the convex hull of the union of the active subdifferentials. -/
theorem subdifferential_pointwise_max_eq_convexHull_iUnion_active_subdifferential
    (f : ι → E → EReal) (x : E)
    (h_ne_bot : ∀ i : ι, ∀ y : E, f i y ≠ ⊥)
    (hconvex : ∀ i : ι, is_convex_function (f i))
    (hx : x ∈ ⋂ i : ι, interior (effective_domain (f i))) :
    subdifferential (fun y ↦ ⨆ i : ι, f i y) x =
      convexHull ℝ
        (⋃ i : {i : ι // f i x = ⨆ j : ι, f j x}, subdifferential (f i) x) :=
  sorry

end
