import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

/-!
Source/core/bridge triage for this item.

- `source-facing`: the remark records a concrete `WithBotTop ℝ`-valued example on the unit ball,
  with value `-√(1 - ‖x‖²)` on the open unit ball and `+∞` on its boundary and exterior.
- `core/canonical`: the chapter owner abstractions are `Function.IsConvex ℝ`,
  `Function.IsConvex.tendsto_lineMap_to_lowerSemicontinuousHull`, and the affine-combination owner
  `lineMap`.
- `bridge/view`: the textbook formula `(1 - λ) x + λ y` is rendered by `lineMap x y λ`, and the
  source-facing boundary value `0` is the specialization of the closure value `cl(f) y` at points
  with `‖y‖ = 1`.

Domain-style sampling used here:
- `Function.IsConvex` on `WithBotTop ℝ`-valued functions, available from Mathlib/project owners;
- `Function.toWithBotTopOn` for extension by `+∞` outside the open unit ball;
- `Function.IsConvex.tendsto_lineMap_to_lowerSemicontinuousHull` from Theorem 7.5;
- `AffineMap.lineMap` for the segment parameterization.

Primitive data vs derived API:
- primitive data: the explicit formula `x ↦ -√(1 - ‖x‖²)` on the open unit ball, extended by `⊤`
  outside;
- derived API: the convexity theorem for that function and the boundary-limit specialization of the
  Chapter 7 owner theorem.

Layer target: the function definition is `source-facing`; the limit theorem is `bridge/view`,
stated as the concrete boundary-value specialization of the canonical owner theorem from
Theorem 7.5 rather than as a second boundary-limit owner.
-/

variable {E : Type u} [Norm E]

/-- The `WithBotTop ℝ`-valued function equal to `-√(1 - ‖x‖²)` on the open unit ball and `+∞`
outside it. -/
def openUnitBallNegativeSqrtExtension : E → WithBotTop ℝ :=
  Function.toWithBotTopOn
    (fun x : E ↦ -Real.sqrt (1 - ‖x‖ ^ 2))
    {x : E | ‖x‖ < 1}

@[simp] theorem openUnitBallNegativeSqrtExtension_of_norm_lt_one {x : E} (hx : ‖x‖ < 1) :
    openUnitBallNegativeSqrtExtension x =
      ((-(Real.sqrt (1 - ‖x‖ ^ 2)) : ℝ) : WithBotTop ℝ) := by
  simpa [openUnitBallNegativeSqrtExtension] using
    (Function.toWithBotTopOn_of_mem
      (fun y : E ↦ -Real.sqrt (1 - ‖y‖ ^ 2))
      {y : E | ‖y‖ < 1} hx)

@[simp] theorem openUnitBallNegativeSqrtExtension_of_one_le_norm {x : E} (hx : 1 ≤ ‖x‖) :
    openUnitBallNegativeSqrtExtension x = (⊤ : WithBotTop ℝ) := by
  exact
    Function.toWithBotTopOn_of_notMem
      (fun y : E ↦ -Real.sqrt (1 - ‖y‖ ^ 2))
      {y : E | ‖y‖ < 1}
      (by simpa using (not_lt_of_ge hx))

end

section

open AffineMap Filter
open scoped Rockafellar

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local notation "fUnit" => (openUnitBallNegativeSqrtExtension (E := E))

-- Proof sketch: this is the canonical Chapter-7 owner theorem specialized to the present
-- source-facing function, with endpoint hypothesis on the intrinsic closure of the effective
-- domain.
/-- Canonical owner-level segment-limit statement for `openUnitBallNegativeSqrtExtension`: from
`x ∈ riDom[ℝ](f)` toward any endpoint `y ∈ intrinsicClosure ℝ dom(f)`, the profile along
`lineMap x y` converges to `cl(f) y` as `t → 1⁻`. -/
theorem tendsto_openUnitBallNegativeSqrtExtension_lineMap_left_to_cl_of_mem_intrinsicClosure_dom
    {x y : E} (hconv : Function.IsConvex ℝ fUnit) (hx : x ∈ riDom[ℝ](fUnit))
    (hy : y ∈ intrinsicClosure ℝ dom(fUnit)) :
    Tendsto (fun t : ℝ ↦ fUnit (lineMap x y t))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (cl(fUnit) y)) := by
  simpa using
    (Function.IsConvex.tendsto_lineMap_to_lowerSemicontinuousHull_of_mem_intrinsicClosure_dom
      (f := fUnit) hconv (x := x) (y := y) hx hy)

-- Proof sketch: as `t → 1⁻`, the points `AffineMap.lineMap x y t` approach the boundary point
-- `y`. The quantity `1 - ‖AffineMap.lineMap x y t‖²` tends to `0` through nonnegative values, so
-- the interior branch `-√(1 - ‖·‖²)` tends to `0`, which is the boundary value of the
-- lower-semicontinuous hull predicted by Theorem 7.5.
/-- At a boundary point `y` with `‖y‖ = 1`, the segment profile of
`openUnitBallNegativeSqrtExtension` from any `x ∈ riDom[ℝ](fUnit)` tends to `0` as the parameter
approaches `1` from the left. -/
theorem tendsto_openUnitBallNegativeSqrtExtension_lineMap_left_to_zero_of_norm_eq_one
    {x y : E} (hx : x ∈ riDom[ℝ](fUnit)) (hy : ‖y‖ = 1) :
    Tendsto (fun t : ℝ ↦ fUnit (lineMap x y t))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (0 : WithBotTop ℝ)) := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "fUnit" => (openUnitBallNegativeSqrtExtension (E := E))

-- Proof sketch: the function is smooth on the open unit ball, hence convex on the interior of its
-- effective domain. The companion boundary-limit theorem supplies the Theorem-7.5 style limit
-- relation at points with `‖y‖ = 1`, which is the use of Theorem 7.5 highlighted by the remark
-- for this explicit example.
/-- Remark 7.0.25: the `WithBotTop ℝ`-valued function that equals `-√(1 - ‖x‖²)` on the open unit
ball and `+∞` for `‖x‖ ≥ 1` is convex. -/
theorem openUnitBallNegativeSqrtExtension_isConvex :
    Function.IsConvex ℝ fUnit := sorry

end
