import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_6_5
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_7_1
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_7_2
import LecturesConvexOptimization_Nesterov_2018.Chap05.RealProdL2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped PowerConeGeometricMean

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

open scoped PowerCone

/- Theorem 5.4.7.3 is a barrier theorem in the Chapter 5 power-cone domain.

Sampled owner declarations:
* `powerCone` from `Definition_5_4_7_1`, the earlier source-facing owner for `K_α`;
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the generic owner for the composed barrier
  used here;
* `power_cone_plus_barrier_apply` from `Theorem_5_4_7_4`, the adjacent bridge theorem evaluating
  the one-sided specialization of the same generic owner shape;
* `ξ[α]`, `powerConeBarrier`, and the swapped-coordinate specialization
  `secondOrderConeBarrier ∘ Prod.swap`, the earlier primitive factor data for the same
  cone-composition construction;
* `powerConeGeometricMean_isOneCompatibleWith_powerConeBarrier` from `Theorem_5_4_7_2`, the
  compatibility theorem feeding the proof route.

Source/core/bridge triage:
* source-facing: the barrier owner `power_cone_barrier α` and the resulting four-self-concordant
  barrier statement on `powerCone α`;
* core/canonical: the earlier owner `coneCompositionBarrier` specialized to the power-cone data;
* bridge/view: the explicit logarithmic evaluation formula below.

Primitive data:
* `powerConeBarrier`;
* `secondOrderConeBarrier ∘ Prod.swap`;
* `ξ[α]`;
* the source-facing cone owner `powerCone α`.

Derived API:
* the source-facing barrier owner `power_cone_barrier α`;
* the pointwise evaluation formula below;
* the resulting `4`-self-concordant barrier statement on `interior (powerCone α)`.

This refinement keeps `coneCompositionBarrier` as the core owner abstraction for the proof route,
but exposes the textbook power-cone barrier itself through the shorter source-facing owner
`power_cone_barrier α`, matching the adjacent chapter API. -/

/-- The logarithmic barrier `Ψ_P` for the symmetric power cone `K_α`, presented as the
source-facing specialization of the chapter's canonical cone-composition barrier owner. -/
def power_cone_barrier (α : ℝ) : ((ℝ × ℝ) × ℝ) → ℝ :=
  coneCompositionBarrier
    powerConeBarrier
    (secondOrderConeBarrier ∘ Prod.swap)
    ξ[α]
    1

-- Proof sketch: on the nonnegative orthant, evaluate `power_cone_barrier α` at
-- `((x₁, x₂), z)` using the upstream pointwise formulas for `secondOrderConeBarrier ∘ Prod.swap`,
-- `powerConeBarrier`, and `ξ[α]`, then rewrite the square
-- `(x₁^α x₂^(1 - α))^2` as `x₁^(2 α) x₂^(2 (1 - α))`.
/-- Evaluating `power_cone_barrier α` at `((x₁, x₂), z)` on the nonnegative orthant
reproduces the textbook formula
`-log ((x₁)^(2 α) (x₂)^(2 (1 - α)) - z^2) - log x₁ - log x₂`. -/
theorem power_cone_barrier_apply
    (α x₁ x₂ z : ℝ) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) :
    power_cone_barrier α ((x₁, x₂), z) =
      -Real.log
          (Real.rpow x₁ (2 * α) * Real.rpow x₂ (2 * (1 - α)) - z ^ (2 : ℕ)) -
        Real.log x₁ - Real.log x₂ := by
  rw [power_cone_barrier, coneCompositionBarrier_apply, secondOrderConeBarrier_swap_apply,
    powerConeBarrier_apply, powerConeGeometricMean_apply]
  norm_num
  have hx₁_square : Real.rpow x₁ α ^ (2 : ℕ) = Real.rpow x₁ (α * 2) := by
    simpa using (Real.rpow_mul_natCast hx₁ α 2).symm
  have hx₂_square : Real.rpow x₂ (1 - α) ^ (2 : ℕ) = Real.rpow x₂ ((1 - α) * 2) := by
    simpa using (Real.rpow_mul_natCast hx₂ (1 - α) 2).symm
  have hsquare :
      (Real.rpow x₁ α * Real.rpow x₂ (1 - α)) ^ (2 : ℕ) =
        Real.rpow x₁ (2 * α) * Real.rpow x₂ (2 * (1 - α)) := by
    calc
      (Real.rpow x₁ α * Real.rpow x₂ (1 - α)) ^ (2 : ℕ) =
          (Real.rpow x₁ α) ^ (2 : ℕ) * (Real.rpow x₂ (1 - α)) ^ (2 : ℕ) := by
            ring
      _ = Real.rpow x₁ (α * 2) * Real.rpow x₂ ((1 - α) * 2) := by
        rw [hx₁_square, hx₂_square]
      _ = Real.rpow x₁ (2 * α) * Real.rpow x₂ (2 * (1 - α)) := by
        congr 1 <;> ring_nf
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    congrArg
      (fun t : ℝ ↦ -Real.log (t - z ^ (2 : ℕ)) + (-Real.log x₁ - Real.log x₂))
      hsquare

-- Proof sketch: apply the cone-composition barrier construction with
-- `Q₁ = ℝ_+²`, `F(x₁, x₂) = -log x₁ - log x₂`, `β = 1`, `ξ(x₁, x₂) = x₁^α x₂^(1 - α)`, and
-- `Φ(y, z) = -log (y^2 - z^2)`. Theorem 5.4.7.2 supplies the `1`-compatibility of `ξ` with
-- `F`, and the planar barrier `Φ` has parameter `μ = 2`; together with `ν = 2` for `F`, the
-- composed barrier has parameter `μ + ν = 4` and specializes to the owner barrier below on the
-- interior of `powerCone α`.
/-- Theorem 5.4.7.3: for `0 < α < 1`, the function
`Ψ_P((x₁, x₂), z) = -log ((x₁)^(2 α) (x₂)^(2 (1 - α)) - z^2) - log x₁ - log x₂`
is a `4`-self-concordant barrier for the power cone `K_α`. -/
theorem power_cone_barrier_is_four_self_concordant_barrier
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsSelfConcordantBarrierOnWith
      (interior K_[α])
      (4 : NNReal)
      (power_cone_barrier α) := sorry
