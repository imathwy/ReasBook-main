import Mathlib
import Nesterov.Chap05.RealProdL2
import Nesterov.Chap05.Theorem_5_3_3
import Nesterov.Chap05.Definition_5_3_2
import Nesterov.Chap05.Definition_5_4_8_15
import Nesterov.Chap05.Definition_5_4_8_16

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

variable (p : ℝ)

/- Theorem 5.4.8.7 lies in the Chapter 5 self-concordant-barrier / power-cone-slice domain.

Sampled owner declarations:
* `constrainedEpigraph` and `mem_Q₆_iff` from `Definition_5_4_8_15`, the source-facing
  owner/view for `Q₆`;
* `separableLogBarrierF6` from `Definition_5_4_8_16`, the source-facing owner for `F₆`;
* `power_cone_plus_barrier_is_three_self_concordant_barrier` from `Theorem_5_4_7_4`, the
  upstream one-sided power-cone barrier theorem;
* `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` from `Theorem_5_3_3`, the canonical
  affine-pullback theorem for barrier owners.

Best owner abstraction:
* source-facing: the textbook epigraph `Q₆` and barrier `F₆`;
* core/canonical: `K_[p / (p + 1)]⁺`,
  `power_cone_plus_barrier (p / (p + 1))`, and
  `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap`;
* bridge/view: the affine unit slice `q ↦ (q, 1)`.

Primitive data:
* the canonical epigraph owner specialized to `x ↦ x⁻ᵖ`;
* the canonical source-facing barrier owner `separableLogBarrierF6 p`.

Derived API:
* the interior-membership theorem for `Q₆`;
* the unit-slice bridge from `K_[p / (p + 1)]⁺` to `Q₆`;
* the direct definitional unit-slice realization of `F₆`;
* the resulting source-facing barrier theorem.

This refinement keeps `Q₆` and `F₆` source-facing, but removes the ad hoc public ambient-instance
parameters and presents the theorem through the canonical one-sided power-cone owner already used
upstream in the chapter. -/

local notation "F₆" => separableLogBarrierF6 p

-- Proof sketch: rewrite Definition 5.4.8.15 through the chapter owner
-- `constrainedEpigraph`; the interior of this closed epigraph is obtained by keeping the
-- positivity condition `x > 0` and replacing the boundary inequality `t ≥ 1 / x^p`
-- with the strict inequality `t > 1 / x^p`.
/-- A pair `(x, t)` lies in the interior of the canonical epigraph for Definition 5.4.8.15
exactly when `x > 0` and `t > x^{-p}`. -/
theorem mem_interior_qSix_iff {x t : ℝ} :
    (x, t) ∈ interior (Q₆ p) ↔
      0 < x ∧ t > 1 / Real.rpow x p := sorry

-- Proof sketch: for `α = p / (p + 1)`, the unit slice `((x, t), 1)` of the one-sided power cone
-- condition `1 ≤ x^α t^(1 - α)` is equivalent to `t ≥ x^{-p}` when `p > 0`. Since membership in
-- `Q₆` already records `x > 0`, the positivity of `t` is then automatic.
/-- On the affine slice `((x, t), 1)`, the one-sided power cone with
`α = p / (p + 1)` is exactly the canonical epigraph `Q₆`. -/
theorem mem_power_cone_plus_unitSlice_qSix_iff {x t : ℝ} (hp : 0 < p) :
    ((x, t), 1) ∈ K_[(p / (p + 1))]⁺ ↔ (x, t) ∈ Q₆ p := sorry

-- Proof sketch: the interior of `Q₆` is the strict version of its epigraph inequalities, and the
-- same strict inequalities describe the unit slice of `interior (K_[(p / (p + 1))]⁺)`.
/-- On the affine slice `((x, t), 1)`, membership in `interior (K_[(p / (p + 1))]⁺)`
is exactly membership in `interior Q₆`. -/
theorem mem_interior_power_cone_plus_unitSlice_qSix_iff {x t : ℝ} (hp : 0 < p) :
    ((x, t), 1) ∈ interior (K_[(p / (p + 1))]⁺) ↔ (x, t) ∈ interior (Q₆ p) := sorry

-- Proof sketch: rewrite the interior of the canonical epigraph from Definition 5.4.8.15 as
-- the strict domain
-- `{(x, t) | x > 0, t > x^{-p}}`, set `α = p / (p + 1) ∈ (0, 1)`, and observe that
-- `t ≥ x^{-p}` is equivalent to `x^α t^(1 - α) ≥ 1`. Then identify `separableLogBarrierF6 p`
-- with the affine slice `z = 1` of the standard `3`-self-concordant barrier for the lifted
-- one-sided power cone, and use preservation of self-concordance under affine restriction.
/-- Theorem 5.4.8.7: for `p > 0`, the function
`F₆(x, t) = -\log x - \log t - \log (x^α t^(1 - α) - 1)` with `α = p / (p + 1)` is a
`3`-self-concordant barrier for
`Q₆ = {(x, t) ∈ \mathbb{R}^2 \mid x > 0,\ t ≥ x^{-p}}`. -/
theorem separableLogBarrierF6_is_three_selfConcordantBarrier
    (hp : 0 < p) :
    IsSelfConcordantBarrierOnWith (interior (Q₆ p)) (3 : NNReal) F₆ := by
  let α : ℝ := p / (p + 1)
  have hα₀ : 0 < α := sorry
  have hα₁ : α < 1 := sorry
  let g : (ℝ × ℝ) →ᴬ[ℝ] ((ℝ × ℝ) × ℝ) :=
    ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod
        (0 : (ℝ × ℝ) →L[ℝ] ℝ)).toContinuousAffineMap +ᵥ
      ContinuousAffineMap.const ℝ (ℝ × ℝ) (((0 : ℝ), (0 : ℝ)), (1 : ℝ))
  have hg_apply (q : ℝ × ℝ) : g q = (q, 1) := by
    simp [g]
  let hbase :
      IsSelfConcordantBarrierOnWith
        (interior (K_[α]⁺))
        (3 : NNReal)
        (power_cone_plus_barrier α) :=
    power_cone_plus_barrier_is_three_self_concordant_barrier hα₀ hα₁
  let hslice :
      IsSelfConcordantBarrierOnWith
        (g ⁻¹' interior (K_[α]⁺))
        (3 : NNReal)
        (power_cone_plus_barrier α ∘ g) :=
    hbase.comp_continuousAffineMap g
  have hdom : g ⁻¹' interior (K_[α]⁺) = interior (Q₆ p) := by
    ext q
    change g q ∈ interior (K_[α]⁺) ↔ q ∈ interior (Q₆ p)
    rw [hg_apply]
    simpa [α] using mem_interior_power_cone_plus_unitSlice_qSix_iff p hp
  have hfun : power_cone_plus_barrier α ∘ g = F₆ := by
    funext q
    change power_cone_plus_barrier α (g q) = separableLogBarrierF6 p q
    simp [hg_apply, separableLogBarrierF6, α]
  simpa [hdom, hfun, α] using hslice
