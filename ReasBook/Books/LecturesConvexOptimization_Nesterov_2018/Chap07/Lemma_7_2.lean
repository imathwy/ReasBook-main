import Nesterov.Chap03.Definition_3_9
import Nesterov.Chap03.Definition_3_20

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SupportFunction

universe u v

/-
Lemma 7.2 lies in the chapter's support-function / dual-norm comparison domain.

Sampled owner-style declarations:
- Chapter 3 `ξ[Q]` and `supportFunction_apply`
- Chapter 3 `Seminorm.dualNorm` and `Seminorm.dualNorm_apply`
- mathlib `Seminorm.closedBall`
- mathlib `Seminorm.closedBall_zero_eq`

Best owner abstraction:
- source-facing: the support-function bound for `x ↦ (ξ[Q₂] (A x)).toReal`
- core/canonical: `ξ[Q₂]`, `Seminorm.dualNorm`, and `Seminorm.closedBall`
- bridge/view: the real-valued `toReal` surface of `ξ[Q₂]`

Primitive data:
- a real-linear map `A : X →ₗ[ℝ] F`
- a set `Q₂ : Set F`
- a seminorm `p : Seminorm ℝ F` with `[Seminorm.IsNorm p]`
- radii `γ₀`, `γ₁`

Derived API:
- the dual norm `p.dualNorm`
- the primal balls `p.closedBall 0 γ`
- the pointwise real-valued support function `x ↦ (ξ[Q₂] (A x)).toReal`

Source/core/bridge triage:
- source-facing: the sandwich estimate for the support function of `Aᵀ Q₂`
- core/canonical: the Chapter 3 support-function and dual-norm owners
- bridge/view: precomposition with `A` and the `toReal` passage for the support function

This refinement deletes the duplicate local owners `VectorNorm`, `supportFunction`,
`supportFunctionAlongLinearMap`, and `pulledDualNorm`. The public statement now uses the chapter
owners directly and only keeps the real-valued `toReal` bridge because the textbook inequality is
real-valued.
-/

section

variable {X : Type v} [AddCommGroup X] [Module ℝ X]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-
Proof sketch: compare `ξ[Q₂]` with the support functions of the inner and outer `p`-balls using
`p.closedBall 0 γ₀ ⊆ Q₂ ⊆ p.closedBall 0 γ₁`; then identify the support functions of those balls
with `γ₀` and `γ₁` times `p.dualNorm`. The only explicit radius sign assumption needed in the public
API is `0 ≤ γ₀`: since `0 ∈ p.closedBall 0 γ₀`, the inclusions force `0 ∈ p.closedBall 0 γ₁`, so
`0 ≤ γ₁` is derived internally from the canonical closed-ball owner. -/
/-- Lemma 7.2: if `Q₂` contains the `p`-ball of radius `γ₀` and is contained in the `p`-ball of
radius `γ₁`, then the real-valued support function of `Aᵀ Q₂ = ∂f(0)` is sandwiched between `γ₀`
and `γ₁` times the pulled-back dual norm `x ↦ ‖A x‖_*`. The pointwise sandwich only needs the
inner radius to be explicitly nonnegative; the outer-radius nonnegativity follows from the two ball
inclusions. The stronger positivity hypotheses needed for the ratio `γ₀ / γ₁` are kept separate in
`gammaRatio_pos_and_le_one`. -/
theorem supportFunction_toReal_comp_linearMap_dualNorm_bounds
    (A : X →ₗ[ℝ] F) (Q2 : Set F) (p : Seminorm ℝ F) [Seminorm.IsNorm p]
    (γ₀ γ₁ : ℝ) (hγ₀_nonneg : 0 ≤ γ₀)
    (hQ2_lower : p.closedBall 0 γ₀ ⊆ Q2)
    (hQ2_upper : Q2 ⊆ p.closedBall 0 γ₁)
    (x : X) :
    γ₀ * p.dualNorm (A x) ≤ (ξ[Q2] (A x)).toReal ∧
      (ξ[Q2] (A x)).toReal ≤ γ₁ * p.dualNorm (A x) := sorry

-- Proof sketch: `0 < γ₀ ≤ γ₁` implies `0 < γ₁`, hence division by `γ₁` preserves order and gives
-- `0 < γ₀ / γ₁ ≤ 1`.
/-- The ratio `γ₀ / γ₁` is positive and at most `1`, which is the numerical content used for the
choice `α = γ₀ / γ₁` in the relative-scale condition. -/
theorem gammaRatio_pos_and_le_one {γ₀ γ₁ : ℝ}
    (hγ₀ : 0 < γ₀) (hγ₀γ₁ : γ₀ ≤ γ₁) :
    0 < γ₀ / γ₁ ∧ γ₀ / γ₁ ≤ 1 := sorry

end
