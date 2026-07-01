import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Corollary_23_5_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Example_23_0_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Function

variable {C : Set E} {x xStar : E}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 23.5.3 identifies subgradients of the support function of a nonempty
  closed convex set with the points of the set where the corresponding linear functional attains
  its maximum.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.subdifferentialAt` and the support-function owner
  `(δᵛ[WithBotTop ℝ](· | C) : E → WithBotTop ℝ)`.
- `bridge/view`: the proof reuses the existing chapter bridge chain
  `supportFunction = (indicatorFunction C)⋆`,
  `Function.IsClosedProperConvex.mem_subdifferentialAt_convexConjugate_iff`,
  and `Function.mem_subdifferentialAt_indicatorFunction_iff`.

Domain-style sampling used here:
- `supportFunction` / `δᵛ(· | C)` from `Chap01/Defintion_4_8_2`;
- `indicatorFunction_isClosedProperConvex_of_nonempty` from `Chap03/Text_12_3_6`;
- `convexConjugate_indicatorFunction_eq_supportFunction` from `Chap03/Text_13_1_4`;
- `Function.IsClosedProperConvex.mem_subdifferentialAt_convexConjugate_iff` and
  `Function.mem_subdifferentialAt_indicatorFunction_iff` from Chapter 23.

Primitive data vs derived API:
- primitive inputs: the set `C`, the primal point `x`, the dual point `xStar`, and the
  nonempty/closed/convex hypotheses on `C`;
- derived API: the equivalence between support-function subgradient membership and the primal
  maximizer condition on `C`.

Layer target: `source-facing`. The public theorem remains the textbook set-level statement on the
owner `(δᵛ[WithBotTop ℝ](· | C) : E → WithBotTop ℝ)`, while the proof is routed through the
canonical indicator owner instead of a second local Fenchel-Young unpacking.
-/

-- Proof sketch: the indicator of a nonempty closed convex set is a closed proper convex function,
-- so Corollary 23.5.1 applies to `δ(· | C)`. Rewrite its conjugate as `supportFunction C`, then
-- rewrite the remaining indicator-subgradient clause by the existing source-facing owner theorem
-- `Function.mem_subdifferentialAt_indicatorFunction_iff`. The resulting sign inequality is exactly
-- the pointwise `IsMaxOn` condition for `z ↦ ⟪z, xStar⟫` on `C`.
/-- Corollary 23.5.3: for a nonempty closed convex set `C`, a point `x` belongs to the
subdifferential of the support function `δᵛ[WithBotTop ℝ](· | C)` at `xStar` exactly when `x ∈ C`
and the linear functional `z ↦ ⟪z, xStar⟫` attains its maximum over `C` at `x`. In the source
notation, this is the subdifferential of `δᵛ(· | C)`. -/
theorem mem_subdifferentialAt_supportFunction_iff_mem_and_isMaxOn
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    x ∈ subdifferentialAt (δᵛ[WithBotTop ℝ](· | C)) xStar ↔
      x ∈ C ∧ IsMaxOn (fun z : E ↦ ⟪z, xStar⟫) C x := by
  have h_indicator : (δ(· | C) : E → EReal).IsClosedProperConvex :=
    indicatorFunction_isClosedProperConvex_of_nonempty hC_nonempty hC_closed hC_convex
  rw [← convexConjugate_indicatorFunction_eq_supportFunction C]
  rw [h_indicator.mem_subdifferentialAt_convexConjugate_iff]
  rw [mem_subdifferentialAt_indicatorFunction_iff]
  constructor
  · rintro ⟨hxC, hxStar⟩
    refine ⟨hxC, isMaxOn_iff.2 ?_⟩
    intro z hzC
    exact sub_nonpos.mp <| by
      simpa [real_inner_comm, inner_sub_right] using hxStar z hzC
  · rintro ⟨hxC, hmax⟩
    refine ⟨hxC, ?_⟩
    intro z hzC
    have hz : (⟪z, xStar⟫ : ℝ) ≤ ⟪x, xStar⟫ :=
      (isMaxOn_iff.mp hmax) z hzC
    simpa [real_inner_comm, inner_sub_right] using sub_nonpos.mpr hz

end Function

end
