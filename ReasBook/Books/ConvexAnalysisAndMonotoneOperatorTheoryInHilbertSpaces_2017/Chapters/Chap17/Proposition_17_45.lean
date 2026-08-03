import BauschkeLean.Chap16.Proposition_16_27
import BauschkeLean.Chap17.Proposition_17_31

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Gradient

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 17.45 identifies singleton subdifferentials with Fréchet
  differentiability and the corresponding gradient, without assuming
  `x ∈ interior (effectiveDomain f)` in the theorem header.
- `core/canonical`: the owner abstractions are `DifferentiableAt`, `HasGradientAt`, and `∇`;
  the interior-domain point is recovered from the singleton hypothesis in the source proof.
- `bridge/view`: `HasGradientAt ... u x` packages the source-facing conjunction
  `DifferentiableAt ... x ∧ u = ∇ ... x`.
-/

-- Semantic recall: `lean_leansearch` only surfaced generic calculus lemmas, while the verified
-- Chapter 17 precedent for this item packages the Fréchet side through `DifferentiableAt`,
-- `HasGradientAt`, and `∇`.
-- Proof sketch: if `(∂ f) x = {u}`, the source proof first derives
-- `x ∈ interior (effectiveDomain f)`, then applies Proposition 17.31 (2) and Corollary 17.44 to
-- obtain Fréchet differentiability with gradient `u`. Conversely, a Fréchet gradient gives the
-- corresponding Gâteaux derivative, and Proposition 17.31 (1) identifies the singleton
-- subdifferential with that gradient.

/-- Proposition 17.45: on a finite-dimensional real Hilbert space, for `f ∈ Γ₀(H)`,
`(∂ f) x = {u}` if and only if the finite representative of `f` is Fréchet differentiable at `x`
and `u = ∇ (fun y ↦ (f y : EReal).toReal) x`. -/
theorem subdifferential_eq_singleton_iff_differentiableAt_and_eq_gradient_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (u : H) :
    (∂ f) x = ({u} : Set H) ↔
      DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x ∧
        u = ∇ (fun y ↦ (f y : EReal).toReal) x := sorry

/-- Canonical `HasGradientAt` reformulation of Proposition 17.45. -/
theorem subdifferential_eq_singleton_iff_hasGradientAt_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (u : H) :
    (∂ f) x = ({u} : Set H) ↔
      HasGradientAt (fun y ↦ (f y : EReal).toReal) u x := sorry

end DifferentiabilityOfConvexFunctions

end ERealFunction
