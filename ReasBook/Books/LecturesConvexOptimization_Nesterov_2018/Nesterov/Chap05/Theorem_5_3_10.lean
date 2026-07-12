import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_20
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_3_2
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_3_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: let `x*(t)` be the exact minimizer of the penalty objective. Apply the
-- first-order optimality condition for `x*(t)` and compare it with an optimal solution `xOpt`
-- of the original linear problem on `closure dom`. The barrier inequality against the chord from
-- `x*(t)` to `xOpt`, together with `closure dom` as the closed feasible set, yields the estimate
-- `⟪c, x*(t)⟫ - ⟪c, xOpt⟫ ≤ ν / t`.
/-- For an exact central-path point at parameter `t > 0`, the objective gap to any optimal point
of the original linear problem on `closure dom` is at most `ν / t`. -/
theorem centralPathPoint_objectiveGap_le_barrierParameter_div
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ))
    (xOpt : closure dom)
    (hopt : ∀ y : closure dom, inner ℝ c (xOpt : E) ≤ inner ℝ c (y : E))
    {xPath : dom}
    (hpath : IsMinOn (centralPathPenaltyObjective c F t) dom (xPath : E)) :
    inner ℝ c (xPath : E) - inner ℝ c (xOpt : E) ≤ (ν : ℝ) / (t : ℝ) := sorry

-- Proof sketch: compare the approximate center `x` with an exact penalty minimizer `xPath` at
-- the same parameter `t`. The approximate-centering hypothesis bounds the primal error
-- `t ⟪c, x - xPath⟫` by the Newton-decrement correction
-- `((β + √ν) β) / (1 - β)`, while
-- `centralPathPoint_objectiveGap_le_barrierParameter_div` controls the exact central-path gap
-- `⟪c, xPath⟫ - ⟪c, xOpt⟫` by `ν / t`. Adding the two bounds gives the stated estimate.
/-- Theorem 5.3.10: if `xPath` is an exact central-path point for the penalty objective
`z ↦ t ⟪c, z⟫ + F z` at some `t > 0`, and if another point `x` in `dom` satisfies the
approximate-centering condition
`‖t c + ∇ F(x)‖*ₓ ≤ β` with `β < 1`, then the objective gap from `x` to any optimal point
`xOpt ∈ closure dom` is bounded by
`(ν + ((β + √ν) β) / (1 - β)) / t`. In particular, the exact central-path gap is recovered by
the companion theorem above. -/
theorem centralPathApproximateCenter_objectiveGap_le_barrierParameter_add_error_div
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) (t : Set.Ici (0 : ℝ)) {β : ℝ} (ht : 0 < (t : ℝ)) (hβ : β < 1)
    (xOpt : closure dom)
    (hopt : ∀ y : closure dom, inner ℝ c (xOpt : E) ≤ inner ℝ c (y : E))
    {xPath x : dom}
    (hpath : IsMinOn (centralPathPenaltyObjective c F t) dom (xPath : E))
    (hxH : (fderiv ℝ (∇ F) (x : E)).det ≠ 0)
    (happrox :
      HessianDualLocalNorm.ofDetNeZero F (x : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hxH
        ((InnerProductSpace.toDual ℝ E) ((t : ℝ) • c + ∇ F (x : E))) ≤ β) :
    inner ℝ c (x : E) - inner ℝ c (xOpt : E) ≤
      ((ν : ℝ) + ((β + Real.sqrt (ν : ℝ)) * β) / (1 - β)) / (t : ℝ) := sorry

end
