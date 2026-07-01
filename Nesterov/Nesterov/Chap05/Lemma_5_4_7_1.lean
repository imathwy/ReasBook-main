import Mathlib
import Nesterov.Chap05.Definition_5_4_7_4
import Nesterov.Chap05.RealProdL2
import Nesterov.Chap05.Theorem_5_4_1_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProdProd

open scoped PowerConePlus

/- Lemma 5.4.7.1 lies in the Chapter 5 power-cone / self-concordant-barrier domain.

Sampled owner declarations:
* `power_cone_plus` from `Definition_5_4_7_4`, the source-facing owner for the one-sided power
  cone `K_α^+`;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier;
* `IsSelfConcordantBarrierOnWith.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions`
  from `Theorem_5_4_1_2`, the canonical barrier-parameter lower-bound owner theorem;
* `Chap05RealProdL2.instInnerProductSpaceRealProdProd` from `RealProdL2`, the chapter owner
  bridge equipping the raw triple model `((ℝ × ℝ) × ℝ)` with the canonical Euclidean `L²`
  ambient structure needed by the barrier owner theorem.

Source/core/bridge triage:
* source-facing: the lower bound `ν ≥ 3` for barriers on `K_[α]⁺`;
* core/canonical: the barrier owner
  `IsSelfConcordantBarrierOnWith (interior (K_[α]⁺)) ν F`;
* bridge/view: the shared `RealProdL2` ambient-instance activation together with the proof-level
  recession directions `((1, 0), 0)`, `((0, 1), 0)`, and `((0, 0), -1)` and the auxiliary point
  family `((1, 1), -τ)`.

Primitive data:
* the source-facing cone owner `K_[α]⁺`;
* the barrier owner `hF : IsSelfConcordantBarrierOnWith (interior (K_[α]⁺)) ν F`.

Derived API:
* the source-facing lower bound `(3 : ℝ) ≤ (ν : ℝ)`.

The source-facing cone owner `K_[α]⁺` remains the public surface. This file now reuses the
chapter-wide `RealProdL2` ambient bridge instead of repeating local `WithLp` instance blocks, and
the explicit recession directions remain proof-only data rather than public API. -/

-- Proof sketch: apply
-- `barrierParameter_ge_sum_alpha_div_beta_of_recession_directions` directly to the cone
-- `K_[α]⁺` with recession directions `((1, 0), 0)`, `((0, 1), 0)`, and
-- `((0, 0), -1)`, base point `((1, 1), -τ)`, and coefficients
-- `α₁ = α₂ = β₁ = β₂ = 1`, `α₃ = τ`, `β₃ = 1 + τ`. This gives
-- `ν ≥ 2 + τ / (1 + τ)`. Under the contradiction hypothesis `ν < 3`, choosing
-- `τ = ν / (3 - ν)` turns this into `2 + ν / 3 ≤ ν`, which is impossible.
/-- Lemma 5.4.7.1: for `0 < α < 1`, every `ν`-self-concordant barrier for the one-sided power
cone `K_α^+` has barrier parameter at least `3`. -/
theorem power_cone_plus_barrierParameter_ge_three
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    {ν : NNReal} {F : ((ℝ × ℝ) × ℝ) → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (interior (K_[α]⁺)) ν F) :
    (3 : ℝ) ≤ (ν : ℝ) := by
  sorry
