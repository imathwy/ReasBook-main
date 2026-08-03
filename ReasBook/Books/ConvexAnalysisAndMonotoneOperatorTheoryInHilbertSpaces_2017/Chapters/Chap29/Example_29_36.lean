import BauschkeLean.Chap29.Proposition_29_35

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open SetValuedOperator
open scoped BigOperators ERealFunction.ProductL2 EuclideanSpace Pointwise

/- Source/core/bridge triage for Example 29.36:
- `source-facing`: the weighted quadratic on `ℝ^N` and the displayed coordinate formulas
  `(29.63)` and `(29.64)`.
- `core/canonical`: the epigraph projection/subgradient solution API from Proposition 29.35.
- `bridge/view`: this file specializes that Chapter 29 owner to the coordinatewise weighted
  quadratic model.
-/
-- Semantic recall: `lean_leansearch` surfaced only generic `EuclideanSpace` owners for finite
-- coordinate sums, so this item is formalized directly as the explicit coordinate specialization
-- of the Proposition 29.35 setup.

/-- The separable weighted quadratic
`x ↦ (1 / 2) * ∑ i, α i * |x i|^2` on `ℝ^N`. -/
noncomputable def weighted_coordinate_quadratic
    {N : ℕ+} (α : Fin N → ℝ) :
    EuclideanSpace ℝ (Fin N) → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * ∑ i, α i * |x i| ^ 2

/-- Evaluating `weighted_coordinate_quadratic` expands to the displayed coordinate sum. -/
@[simp] theorem weighted_coordinate_quadratic_apply
    {N : ℕ+} (α : Fin N → ℝ) (x : EuclideanSpace ℝ (Fin N)) :
    weighted_coordinate_quadratic α x = (1 / 2 : ℝ) * ∑ i, α i * |x i| ^ 2 := rfl

/-- The weighted quadratic is continuous on `ℝ^N`. -/
theorem weighted_coordinate_quadratic_continuous
    {N : ℕ+} (α : Fin N → ℝ) :
    Continuous (weighted_coordinate_quadratic α) := by
  sorry

/-- Coordinatewise nonnegative weights make `weighted_coordinate_quadratic` convex on `ℝ^N`. -/
theorem weighted_coordinate_quadratic_convexOn
    {N : ℕ+} (α : Fin N → ℝ) (hα : ∀ i, 0 ≤ α i) :
    ConvexOn ℝ Set.univ (weighted_coordinate_quadratic α) := by
  sorry

/-- The coordinate system
`ξ_i = ζ_i - (f x - ζ) α_i ξ_i` attached to the weighted quadratic of Example 29.36. -/
def weighted_coordinate_quadratic_system
    {N : ℕ+} (α : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin N)) (ζ : ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : Prop :=
  ∀ i, x i = z i - (weighted_coordinate_quadratic α x - ζ) * α i * x i

/-- Evaluating the weighted-coordinate system at a fixed index recovers the displayed equation. -/
theorem weighted_coordinate_quadratic_system_apply
    {N : ℕ+} {α : Fin N → ℝ} {z : EuclideanSpace ℝ (Fin N)} {ζ : ℝ}
    {x : EuclideanSpace ℝ (Fin N)}
    (hsys : weighted_coordinate_quadratic_system α z ζ x) (i : Fin N) :
    x i = z i - (weighted_coordinate_quadratic α x - ζ) * α i * x i :=
  hsys i

/-- The subgradient inclusion from Proposition 29.35, specialized to the weighted quadratic,
rewrites as the displayed coordinate system of Example 29.36. -/
theorem weighted_coordinate_quadratic_system_of_mem_subgradient_translate
    {N : ℕ+} (α : Fin N → ℝ) (z x : EuclideanSpace ℝ (Fin N)) (ζ : ℝ)
    (hsub :
      z ∈ ({x} : Set (EuclideanSpace ℝ (Fin N))) +
        (weighted_coordinate_quadratic α x - ζ) •
          ((∂ (weighted_coordinate_quadratic α).toEReal) x)) :
    weighted_coordinate_quadratic_system α z ζ x := by
  sorry

/-- Proposition 29.35 specialized to the weighted quadratic: coordinatewise nonnegative weights
already suffice for the first coordinate of the metric projection of `(z, ζ)` onto the epigraph to
satisfy the source coordinate system. -/
theorem weighted_coordinate_quadratic_projection_fst_mem_system_of_not_mem_epigraph
    {N : ℕ+} (α : Fin N → ℝ) (hα : ∀ i, 0 ≤ α i)
    (z : EuclideanSpace ℝ (Fin N)) (ζ : ℝ)
    (hz : (z, ζ) ∉ epigraph (weighted_coordinate_quadratic α).toEReal.asEReal) :
    weighted_coordinate_quadratic_system α z ζ
      (P[epigraph (weighted_coordinate_quadratic α).toEReal.asEReal,
        isChebyshev_epigraph_of_continuous_convex
          (weighted_coordinate_quadratic α)
          (weighted_coordinate_quadratic_continuous α)
          (weighted_coordinate_quadratic_convexOn α hα)] (z, ζ)).1 := by
  let p :=
    P[epigraph (weighted_coordinate_quadratic α).toEReal.asEReal,
      isChebyshev_epigraph_of_continuous_convex
        (weighted_coordinate_quadratic α)
        (weighted_coordinate_quadratic_continuous α)
        (weighted_coordinate_quadratic_convexOn α hα)] (z, ζ)
  simpa [p] using
    weighted_coordinate_quadratic_system_of_mem_subgradient_translate α z p.1 ζ
      (projection_fst_mem_subgradient_translate_of_not_mem_epigraph
        (weighted_coordinate_quadratic α)
        (weighted_coordinate_quadratic_continuous α)
        (weighted_coordinate_quadratic_convexOn α hα)
        z ζ hz)

/-- Example 29.36 (1): for the weighted quadratic
`f x = (1 / 2) * ∑ i, α i * |x i|^2` on `ℝ^N`, once Proposition 29.35 provides a solution
`x̄` of the system `ξ_i = ζ_i - (f x̄ - ζ) α_i ξ_i`, setting `η = f x̄`
yields the coordinate formula; the strict positivity from the source is stronger than needed here,
and coordinatewise nonnegative weights already suffice together with `ζ < η`:
`x̄_i = z_i / (((η - ζ) * α_i) + 1)` for every coordinate `i`, i.e. equation `(29.63)`. -/
theorem weighted_coordinate_quadratic_solution_eq_div
    {N : ℕ+} (α : Fin N → ℝ) (hα : ∀ i, 0 ≤ α i)
    (z : EuclideanSpace ℝ (Fin N)) (ζ : ℝ) (xbar : EuclideanSpace ℝ (Fin N))
    (η : ℝ) (hη : η = weighted_coordinate_quadratic α xbar)
    (hζη : ζ < η)
    (hsys : weighted_coordinate_quadratic_system α z ζ xbar) (i : Fin N) :
    xbar i = z i / (((η - ζ) * α i) + 1) := sorry

/-- Example 29.36 (1), vector form: the solution coordinates are exactly the reciprocally scaled
data `z_i / (((η - ζ) * α_i) + 1)`. -/
theorem weighted_coordinate_quadratic_solution_eq_fun
    {N : ℕ+} (α : Fin N → ℝ) (hα : ∀ i, 0 ≤ α i)
    (z : EuclideanSpace ℝ (Fin N)) (ζ : ℝ) (xbar : EuclideanSpace ℝ (Fin N))
    (η : ℝ) (hη : η = weighted_coordinate_quadratic α xbar)
    (hζη : ζ < η)
    (hsys : weighted_coordinate_quadratic_system α z ζ xbar) :
    xbar = fun i ↦ z i / (((η - ζ) * α i) + 1) := by
  ext i
  simpa using weighted_coordinate_quadratic_solution_eq_div α hα z ζ xbar η hη hζη hsys i

/-- Example 29.36 (2): with `η = f x̄` and the coordinate identity `(29.63)`, the weighted
quadratic value rewrites as the scalar equation
`η = (1 / 2) * ∑ i, α i * (z_i / (((η - ζ) * α_i) + 1))^2`, i.e. equation `(29.64)`. -/
theorem weighted_coordinate_quadratic_eta_eq
    {N : ℕ+} (α : Fin N → ℝ)
    (z : EuclideanSpace ℝ (Fin N)) (ζ : ℝ) (xbar : EuclideanSpace ℝ (Fin N))
    (η : ℝ) (hη : η = weighted_coordinate_quadratic α xbar)
    (hcoord : ∀ i, xbar i = z i / (((η - ζ) * α i) + 1)) :
    η = (1 / 2 : ℝ) * ∑ i, α i * (z i / (((η - ζ) * α i) + 1)) ^ 2 := sorry
