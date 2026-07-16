import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open Metric
open scoped GaugePolar RealInnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.11 identifies the polar gauge of the Euclidean norm with the norm
  itself.
- `core/canonical`: the owner abstraction is the source-facing polar gauge `gauge_polar`, written
  `kᵒ` after `open scoped GaugePolar`.
- `bridge/view`: the norm function `fun x ↦ ((‖x‖ : ℝ) : WithBotTop ℝ)` is compared directly with
  its polar via
  the owner-side majorant and `sInf` formulas, while the displayed Schwarz inequality is the
  standard absolute-value Cauchy-Schwarz estimate.

Domain-style sampling used here:
- `gauge_polar_eq_sInf_nonneg_majorants`;
- `gauge_polar_le_of_majorant`;
- `abs_real_inner_le_norm`;
- `inv_norm_smul_mem_unitClosedBall`.

Primitive data vs derived API:
- primitive source object: the norm function `fun x : E ↦ ((‖x‖ : ℝ) : WithBotTop ℝ)`;
- direct owner reuse: the polar-gauge majorant theorem `gauge_polar_le_of_majorant` and the
  defining `sInf` formula `gauge_polar_eq_sInf_nonneg_majorants`;
- derived bridge: the upper bound from Cauchy-Schwarz and the lower bound from the normalized
  witness `‖x⋆‖⁻¹ • x⋆`.

Layer target: `bridge/view`, since this item does not define a new owner but identifies the norm
with its image under the canonical polar-gauge owner. The proof uses only inner-product-space data,
so the ambient is refined all the way down to arbitrary real inner-product spaces instead of the
concrete `EuclideanSpace ℝ (Fin n)` model or a finite-dimensional specialization.
-/

/- The majorant upper-bound step for `gauge_polar` is already owned upstream. -/
recall gauge_polar_le_of_majorant

/- The defining `sInf` formula for `gauge_polar` is already owned upstream. -/
recall gauge_polar_eq_sInf_nonneg_majorants

/-- Text 15.0.11, in canonical ambient form: the polar gauge of the norm is the norm itself on a
real inner-product space. -/
-- Proof sketch: the upper bound is the owner theorem `gauge_polar_le_of_majorant`, with the
-- majorant `μ⋆ = ‖x⋆‖` supplied by Cauchy-Schwarz. For the lower bound, the defining `sInf`
-- formula says it suffices to test every admissible `μ⋆`; evaluating the admissibility inequality
-- at the normalized vector `‖x⋆‖⁻¹ • x⋆` forces `‖x⋆‖ ≤ μ⋆`.
theorem gauge_polar_norm_eq_norm :
    (fun x : E ↦ ((‖x‖ : ℝ) : WithBotTop ℝ))ᵒ =
      fun x : E ↦ ((‖x‖ : ℝ) : WithBotTop ℝ) := by
  ext xStar
  apply le_antisymm
  · let k : E → WithBotTop ℝ := fun x : E ↦ ((‖x‖ : ℝ) : WithBotTop ℝ)
    let μStar : NNReal := ‖xStar‖₊
    change kᵒ xStar ≤ (μStar : WithBotTop ℝ)
    exact
      gauge_polar_le_of_majorant
        (μStar : ℝ)
        ⟨μStar.2, fun x ↦ by
          have hinner : ⟪x, xStar⟫ ≤ ‖xStar‖ * ‖x‖ := by
            calc
              ⟪x, xStar⟫ ≤ |⟪x, xStar⟫| := le_abs_self _
              _ ≤ ‖x‖ * ‖xStar‖ := abs_real_inner_le_norm x xStar
              _ = ‖xStar‖ * ‖x‖ := by ring
          have hinnerE :
              ((⟪x, xStar⟫ : ℝ) : WithBotTop ℝ) ≤
                ((‖xStar‖ * ‖x‖ : ℝ) : WithBotTop ℝ) := by
            exact WithBotTop.coe_le_coe.mpr hinner
          simpa [WithBot.coe_mul] using hinnerE⟩
  · rw [gauge_polar_eq_sInf_nonneg_majorants]
    refine le_sInf ?_
    rintro _ ⟨μStar, hμ, rfl⟩
    by_cases hx : xStar = 0
    · subst xStar
      have hμ0 : ((0 : ℝ) : WithBotTop ℝ) ≤ (μStar : WithBotTop ℝ) :=
        WithBotTop.coe_le_coe.mpr hμ.1
      simpa using hμ0
    · let y : E := ‖xStar‖⁻¹ • xStar
      have hy_mem : y ∈ Metric.closedBall (0 : E) 1 := by
        simpa [y] using inv_norm_smul_mem_unitClosedBall xStar
      have hy_norm : ‖y‖ ≤ 1 := by
        simpa using (mem_closedBall_zero_iff.mp hy_mem)
      have hyμ :
          ((⟪y, xStar⟫ : ℝ) : WithBotTop ℝ) ≤
            ((μStar * ‖y‖ : ℝ) : WithBotTop ℝ) := by
        simpa [WithBot.coe_mul] using hμ.2 y
      have hy_pair : ⟪y, xStar⟫ = ‖xStar‖ := by
        dsimp [y]
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
        field_simp [norm_ne_zero_iff.mpr hx]
      calc
        ((‖xStar‖ : ℝ) : WithBotTop ℝ) = ((⟪y, xStar⟫ : ℝ) : WithBotTop ℝ) := by rw [hy_pair]
        _ ≤ ((μStar * ‖y‖ : ℝ) : WithBotTop ℝ) := hyμ
        _ ≤ (μStar : WithBotTop ℝ) := by
          have hμy : μStar * ‖y‖ ≤ μStar := by
            nlinarith [hμ.1, hy_norm]
          exact WithBotTop.coe_le_coe.mpr hμy

/- The Schwarz inequality here is already the canonical absolute-value Cauchy-Schwarz estimate. -/
recall abs_real_inner_le_norm

end
