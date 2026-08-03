import BauschkeLean.Chap14.Corollary_14_8
import BauschkeLean.Chap14.Remark_14_4

open scoped Gradient InnerProductSpace Pointwise

noncomputable section

universe u

namespace ERealFunction

section Characterizations

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f g : H → Set.Ioi (⊥ : EReal)}

-- Domain-style sampling:
-- `source-facing`: keep the textbook hypothesis `g = f + q`, with `q = halfSquaredNorm`.
-- `core/canonical`: the owner theorems are the Chapter 14 unit Moreau envelope identity for
-- `(f + q)^*` and the gradient formula `Prox_f = ∇({}^[1] f^*)`.
-- `bridge/view`: substitute `hfg`, rewrite `(f + q)^*`, and then apply the canonical gradient
-- owner directly.

/-- Corollary 24.5.
If `f ∈ Γ₀(ℋ)` and `g = f + q` with `q(x) = ‖x‖² / 2`, then `Prox_f = ∇ g^*`. -/
theorem proximityOperator_eq_gradient_conjugate_of_eq_add_halfSquaredNorm
    (hf : f ∈ Γ₀(H)) (hfg : g = f + halfSquaredNorm) :
    Prox[f, hf] = ∇ (fun y : H ↦ ((g.asEReal∗) y).toReal) := by
  -- Eliminate the source-facing auxiliary function `g` in favor of `f + q`.
  subst g
  -- Rewrite `(f + q)^*` to the Chapter 14 unit Moreau envelope of `f^*`.
  rw [conjugate_add_halfSquaredNorm_eq_unitMoreauEnvelope_gammaZeroConjugate f hf]
  -- Remark 14.4 identifies the gradient of that envelope with `Prox[f, hf]`.
  exact proximityOperator_eq_gradient_conjugateMoreauEnvelope_toReal_of_mem_gammaZero
    (f := f) hf

end Characterizations

end ERealFunction
