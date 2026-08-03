import BauschkeLean.Chap12.Proposition_12_26
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap17.Corollary_17_42

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

section Characterizations

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Source/core/bridge triage:
-- `source-facing`: Proposition 24.1 characterizes the proximal point of `f` through the gradient
--   equation `gradf + p = x`.
-- `core/canonical`: the reusable owner is the residual-subgradient equivalence
--   `p = Prox[f, hf] x ↔ x - p ∈ (∂ f) p`.
-- `bridge/view`: at an interior effective-domain point, the Chapter 17 singleton-subdifferential
--   theorem identifies that residual subgradient with the Gâteaux gradient `gradf`.

/-- Canonical Chapter 24 bridge: a point `p` is the proximal point of `f` at `x` exactly when the
residual `x - p` is a subgradient of `f` at `p`. -/
theorem eq_proximityOperator_iff_sub_mem_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) {x p : H} :
    p = Prox[f, hf] x ↔ x - p ∈ (∂ f) p := by
  constructor
  · intro hp
    have hp_prox : IsProxPoint f x p := by
      simpa [hp] using
        proximityOperator_isProxPoint f (hasUniqueProxPoint_of_mem_gammaZero f hf) x
    rw [mem_subdifferential_iff]
    simpa using
      (isProxPoint_iff_forall_inner_add_le f hf.2 x p).1 hp_prox
  · intro hp_sub
    have hp_prox : IsProxPoint f x p := by
      rw [isProxPoint_iff_forall_inner_add_le f hf.2 x p]
      simpa using (mem_subdifferential_iff f p (x - p)).1 hp_sub
    exact
      eq_proximityOperator_of_isProxPoint f
        (hasUniqueProxPoint_of_mem_gammaZero f hf) hp_prox

/-- Proposition 24.1: if `f ∈ Γ₀(ℋ)` and the finite representative of `f` is Gâteaux
differentiable at an interior effective-domain point `p` with gradient `gradf`, then
`p = Prox_f x` if and only if `gradf + p = x`. -/
theorem eq_proximityOperator_iff_gateauxGradient_add_eq
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) {x p gradf : H}
    (hp : p ∈ interior (effectiveDomain f))
    (hgrad :
      HasGateauxDerivativeAt
        (fun y ↦ (f y : EReal).toReal)
        (toDualMap ℝ H gradf) p) :
    p = Prox[f, hf] x ↔ gradf + p = x := by
  rw [eq_proximityOperator_iff_sub_mem_subdifferential f hf]
  rw [subdifferential_eq_singleton_of_hasGateauxDerivativeAt_of_mem_interior_effectiveDomain
    hf hp hgrad, Set.mem_singleton_iff]
  constructor
  · intro hsub
    calc
      gradf + p = (x - p) + p := by simp [hsub]
      _ = x := by abel_nf
  · intro hxp
    calc
      x - p = (gradf + p) - p := by simp [hxp]
      _ = gradf := by abel_nf

end Characterizations

end ERealFunction
