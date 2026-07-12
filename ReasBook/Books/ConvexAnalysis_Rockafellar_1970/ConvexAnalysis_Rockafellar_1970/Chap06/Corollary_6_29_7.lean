import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Basic
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_7
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_10
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_13
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2

noncomputable section

universe u v w w'

open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type w'}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
variable [HasPairing U UStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "L" => lagrangian (toOrderDual F)

-- Proof sketch: apply the Chapter 7 optimality criterion
-- `isMinOn_objective_iff_exists_zero_mem_subdifferentialAt_lagrangian`, which under the same
-- qualification identifies primal optimal points with existence of a dual vector whose
-- Lagrangian saddle subdifferential contains `0`. Then rewrite that vanishing-subdifferential
-- condition as the saddle-point predicate via Proposition 36.5.2. The source's strict
-- consistency branch is absorbed by the canonical implication
-- `IsStrictlyConsistent.isStronglyConsistent`.
/-- Corollary 6.29.7: under either the closed-convex strong-consistency hypothesis (hence also
under strict consistency) or the polyhedral-consistent hypothesis, a point `x` is an optimal
solution of the convex program associated with `F` if and only if there exists a dual vector
`u⋆` such that `(u⋆, x)` is a saddle-point of the Lagrangian `lagrangian (toOrderDual F)`. -/
theorem isMinOn_objective_iff_exists_isSaddlePoint_lagrangian
    (hqual : (IsClosedConvex F ∧ IsStronglyConsistent 𝕜 F) ∨
      (Function.HasPolyhedralEpigraph (Function.uncurry F) ∧ IsConsistent F)) (x : X) :
    IsMinOn (F)₀ Set.univ x ↔
      ∃ uStar : UStar, IsSaddlePoint L uStar x := sorry

end

end Bifunction
