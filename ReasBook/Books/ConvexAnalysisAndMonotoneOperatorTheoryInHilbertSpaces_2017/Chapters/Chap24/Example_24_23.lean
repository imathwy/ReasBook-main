import BauschkeLean.Chap13.Example_13_41
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap12.Example_12_25
import BauschkeLean.Chap24.Proposition_24_8
import BauschkeLean.Chap29.Example_29_28

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ENNReal EuclideanSpace InnerProductSpace Pointwise

namespace ERealFunction

noncomputable section

-- Source/core/bridge triage:
-- - `source-facing`: Example 24.23 is the proximal formula for the coordinate `ℓ∞` norm.
-- - `core/canonical`: the reusable Chapter 24 proximal owner is the conjugate `ι[C]∗[hιC]` of
--   the `ℓ¹`-ball indicator, together with `Prox[γ, ·, ·]`.
-- - `bridge/view`: this file keeps the source theorem on the `ℓ∞` norm and adds the canonical
--   Chapter 13 bridge identifying that norm with the conjugate of the `ℓ¹`-ball indicator.

section Euclidean

variable {N : ℕ}

local notation "C" => Set.lpClosedUnitBall N 1

/-- The packaged coordinate `ℓ∞` norm on `ℝ^N` is the canonical Fenchel conjugate of the
indicator of the coordinate `ℓ¹` unit ball. -/
theorem lpNormTop_toEReal_eq_conjugate_indicator_lpClosedUnitBall_one :
    (ι[C])∗[indicator_lpClosedUnitBall_mem_gammaZero N 1] =
      (fun y : EuclideanSpace ℝ (Fin N) ↦ ‖y‖_[∞]).toEReal := by
  funext y
  apply Subtype.ext
  change (((ι[C]∗[indicator_lpClosedUnitBall_mem_gammaZero N 1] y : EReal))) =
    (((fun z : EuclideanSpace ℝ (Fin N) ↦ ‖z‖_[∞]).toEReal y : Set.Ioi (⊥ : EReal)) : EReal)
  rw [gammaZeroConjugate_apply, conjugate_indicator_eq_supportFunction]
  have hconj : ENNReal.conjExponent (1 : ℝ≥0∞) = ∞ := by
    simp [ENNReal.conjExponent]
  calc
    σ[C] y =
        (((‖WithLp.toLp (ENNReal.conjExponent (1 : ℝ≥0∞))
          ((EuclideanSpace.equiv (Fin N) ℝ) y)‖ : ℝ) : EReal)) :=
      congrFun (lpDualNorm_eq_lpNorm_conjExponent N 1 le_rfl) y
    _ = (((‖WithLp.toLp ∞ ((EuclideanSpace.equiv (Fin N) ℝ) y)‖ : ℝ) : EReal)) := by
      rw [hconj]
    _ = (((‖(EuclideanSpace.equiv (Fin N) ℝ) y‖ : ℝ) : EReal)) := by
      rw [PiLp.norm_toLp]
    _ = (((fun z : EuclideanSpace ℝ (Fin N) ↦ ‖z‖_[∞]).toEReal y : Set.Ioi (⊥ : EReal)) :
        EReal) := by
      simp [EuclideanSpace.lpNorm]

/-- The packaged coordinate `ℓ∞` norm on `ℝ^N` belongs to `Γ₀`. -/
theorem lpNormTop_toEReal_mem_gammaZero :
    (fun y : EuclideanSpace ℝ (Fin N) ↦ ‖y‖_[∞]).toEReal ∈
      Γ₀(EuclideanSpace ℝ (Fin N)) := by
  letI : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  simpa using lpNorm_toEReal_mem_gammaZero N (∞ : ℝ≥0∞)

/-- Example 24.23: on `ℝ^N`, if `C = Set.lpClosedUnitBall N 1`, then the proximity operator of the
scaled coordinate `ℓ∞` norm satisfies
`Prox[γ, (fun y ↦ ‖y‖_[∞]).toEReal, h∞] x =
  x - γ • projectionPoint C (isChebyshev_lpClosedUnitBall_one N) (γ⁻¹ • x)`. -/
theorem example_24_23_proximityOperator_lpNorm_top_eq_sub_scaled_projection_lpClosedUnitBall_one
    (γ : PosReal) (x : EuclideanSpace ℝ (Fin N)) :
    Prox[
      γ,
      (fun y : EuclideanSpace ℝ (Fin N) ↦ ‖y‖_[∞]).toEReal,
      lpNormTop_toEReal_mem_gammaZero
    ] x =
      x - (γ : ℝ) • projectionPoint C (isChebyshev_lpClosedUnitBall_one N) ((γ : ℝ)⁻¹ • x) :=
    by
  have hscaled_indicator :
      Prox[(γ⁻¹ : PosReal), ι[C], indicator_lpClosedUnitBall_mem_gammaZero N 1] =
        projectionPoint C (isChebyshev_lpClosedUnitBall_one N) := by
    have hsmul_indicator : (γ⁻¹ : PosReal) • ι[C] = ι[C] := by
      funext y
      apply Subtype.ext
      by_cases hy : y ∈ C
      · simp [ERealFunction.indicator, hy]
      · simpa [ERealFunction.indicator, hy] using
          (EReal.coe_mul_top_of_pos (γ⁻¹).2 : (((γ⁻¹ : PosReal) : ℝ) : EReal) * ⊤ = ⊤)
    change
      Prox[
        (γ⁻¹ : PosReal) • ι[C],
        smul_mem_gammaZero (ι[C]) (indicator_lpClosedUnitBall_mem_gammaZero N 1) (γ⁻¹ : PosReal)
      ] =
        projectionPoint C (isChebyshev_lpClosedUnitBall_one N)
    funext y
    simpa [hsmul_indicator] using
      congrArg
        (fun f : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) ↦ f y)
        (proximityOperator_indicator_eq_projectionPoint (isChebyshev_lpClosedUnitBall_one N))
  simpa [lpNormTop_toEReal_eq_conjugate_indicator_lpClosedUnitBall_one, hscaled_indicator]
    using
      (prox_conjugate_eq_sub_scaled_primal_prox
        (indicator_lpClosedUnitBall_mem_gammaZero N 1) γ x)

end Euclidean

end

end ERealFunction
