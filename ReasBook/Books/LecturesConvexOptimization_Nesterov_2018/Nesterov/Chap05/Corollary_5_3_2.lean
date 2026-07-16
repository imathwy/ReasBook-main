import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_3_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_1_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Corollary 5.3.2 lies in the Chapter 5 self-concordant-barrier / recession-direction domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the barrier owner;
* `IsSelfConcordantOnWith.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction` from
  `Theorem_5_1_14`, the canonical self-concordant recession-direction estimate used here;
* `hessianLocalNorm` and `‖u‖[F; x]` from `Definition_5_1_1`, the canonical local-norm owner.

Source/core/bridge triage:
* source-facing: the barrier specialization of the recession-direction estimate;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F`, viewed through its parent
  `IsSelfConcordantOnWith dom 1 F`;
* bridge/view: the barrier-specific derivation of the nonascent and backward-frontier hypotheses
  needed to apply Theorem 5.1.14.

This corollary is a barrier-owner specialization of the Chapter 5 recession-direction estimate, so
its public surface should live on `IsSelfConcordantBarrierOnWith` rather than as a parallel
top-level theorem repeating the owner theorem's name. -/

namespace IsSelfConcordantBarrierOnWith

section

variable {dom : Set E} {ν : NNReal} {F : E → ℝ}
variable {h x : E}

-- Proof sketch: use inequality `(5.3.10)` to show that every recession direction is a
-- nonascent direction for a self-concordant barrier. If the backward ray from `x` in direction
-- `h` hits `frontier dom` at finite distance, apply the owner theorem
-- `IsSelfConcordantOnWith.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction` to the
-- inherited standard self-concordant structure with parameter `1`; if `dom` contains the whole
-- line `x + ℝ • h`, then `F` is constant along that line and both sides vanish.
/-- Corollary 5.3.2: if `F` is a `ν`-self-concordant barrier on `dom` and `h` is a recession
direction of `dom`, then at every `x ∈ dom` the Hessian local norm of `h` is bounded by the
pairing of `h` with the negative gradient. -/
theorem hessianLocalNorm_le_neg_gradient_inner_of_recession_direction
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (hrecession : ∀ ⦃y : E⦄, y ∈ dom → ∀ τ : ℝ, 0 ≤ τ → y + τ • h ∈ dom)
    (hx : x ∈ dom)
    :
    ‖h‖[F; x] ≤ inner ℝ (-∇ F x) h := by
  letI : IsSelfConcordantBarrierOnWith dom ν F := hF
  let hself : IsSelfConcordantOnWith dom 1 F := inferInstance
  sorry

-- Proof sketch: combine the owner-level local-norm bound above with the nonnegativity of the
-- Hessian local norm. This turns the recession-direction estimate into a direct nonpositivity
-- statement for the gradient pairing itself.
/-- For a self-concordant barrier, the gradient pairing with any recession direction of the
domain is nonpositive. -/
theorem inner_gradient_nonpos_of_recession_direction
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (hrecession : ∀ ⦃y : E⦄, y ∈ dom → ∀ τ : ℝ, 0 ≤ τ → y + τ • h ∈ dom)
    (hx : x ∈ dom)
    :
    inner ℝ (∇ F x) h ≤ 0 := by
  have hbound :=
    hF.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction hrecession hx
  have hneg : 0 ≤ inner ℝ (-∇ F x) h :=
    le_trans (hessianLocalNorm_nonneg F x h) hbound
  exact neg_nonneg.mp <| by simpa [inner_neg_left] using hneg

end

end IsSelfConcordantBarrierOnWith

end
