import Mathlib
import Nesterov.Chap05.Definition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.4.1.2 lies in the Chapter 5 self-concordant-barrier / recession-direction domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier;
* `IsSelfConcordantBarrierOnWith.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction`
  in `Corollary_5_3_2`, the owner-level recession-direction estimate used for each `p i`;
* `hessianLocalNorm` and the notation `‖u‖[F; x]` in `Definition_5_1_1`, the canonical Chapter 5
  owner for the Hessian local norm;
* the project’s generic finite-family pattern, for example `Theorem_3_38`, where a finite sum
  lives over `ι : Type*` with `[Fintype ι]` instead of the display model `Fin k`.

Source/core/bridge triage:
* source-facing: the textbook lower bound `∑ i, αᵢ / βᵢ ≤ ν`;
* core/canonical: `IsSelfConcordantBarrierOnWith (interior Q) ν F`;
* bridge/view: the recession-direction lower bounds for each `p i` and the combined gradient
  estimate at `xBar`.

Primitive data:
* the barrier owner `hF : IsSelfConcordantBarrierOnWith (interior Q) ν F`;
* the convex set `Q`, base point `xBar ∈ interior Q`, and recession directions `p i`;
* the finite index owner `[Fintype ι]`, since the theorem uses only finite summation and no order
  or adjacency on the indices;
* the nonnegative scalars `α i`, the positive scalars `β i`, the backward-exit hypotheses, and
  the final point
  `xBar - ∑ i, α i • p i ∈ Q`.

Derived API:
* for each `i`, the owner-level recession-direction estimate
  `1 / β i ≤ ‖p i‖[F; xBar] ≤ ⟪-∇ F xBar, p i⟫`;
* the summed source-facing inequality `∑ i, α i / β i ≤ ν`.

The previous file fixed the ambient space to `EuclideanSpace ℝ (Fin n)` and the finite family to
`Fin k` even though the theorem uses only the real inner-product-space barrier owner and finite
summation. The refined statement keeps the same mathematical semantics while moving the public
surface to the canonical owner namespace, deleting the unnecessary concrete model layer, and
placing the finite family at the generic `[Fintype ι]` owner level. -/

namespace IsSelfConcordantBarrierOnWith

-- Proof sketch: for each recession direction `p i`, apply the recession-direction gradient bound
-- for self-concordant barriers at `xBar` together with the finite backward-step hypothesis
-- `xBar - β i • p i ∉ interior Q` to obtain
-- `1 / β i ≤ ‖p i‖[F; xBar] ≤ ⟪-∇ F xBar, p i⟫`.
-- Then use the basic barrier-parameter inequality with
-- `y = xBar - ∑ i, α i • p i ∈ Q` to get
-- `∑ i α i / β i ≤ ⟪∇ F xBar, xBar - y⟫ ≤ ν`.
/-- Theorem 5.4.1.2: if `Q ⊆ E` is a convex set in a real Hilbert space, `xBar ∈ interior Q`,
`(p i)` is a finite family of recession directions of `Q`, each backward step
`xBar - βᵢ • p i` leaves `interior Q`, and `xBar - ∑ i, α i • p i ∈ Q` for nonnegative scalars
`α i` and positive scalars `β i`, then every `ν`-self-concordant barrier `F` on `interior Q`
satisfies
`∑ i, αᵢ / βᵢ ≤ ν`. -/
theorem barrierParameter_ge_sum_alpha_div_beta_of_recession_directions
    {ι : Type v} [Fintype ι] {Q : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hQ_convex : Convex ℝ Q)
    {xBar : E} (hxBar : xBar ∈ interior Q)
    (p : ι → E)
    (hrecession :
      ∀ i, ∀ ⦃x⦄, x ∈ Q → ∀ t : ℝ, 0 ≤ t → x + t • p i ∈ Q)
    (β α : ι → ℝ)
    (hβ_pos : ∀ i, 0 < β i)
    (hβ_exit : ∀ i, xBar - β i • p i ∉ interior Q)
    (hα_nonneg : ∀ i, 0 ≤ α i)
    (hy : xBar - ∑ i, α i • p i ∈ Q) :
    ∑ i, α i / β i ≤ (ν : ℝ) := sorry

end IsSelfConcordantBarrierOnWith

end
