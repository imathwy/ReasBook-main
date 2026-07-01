import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section Dual

open Metric
open scoped Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Source/core/bridge triage:
- `source-facing`: Text 13.2.4 fixes the unit closed ball `B = {y | ‖y‖ ≤ 1}` and identifies the
  support value at `x*` with `‖x*‖`.
- `core/canonical`: the owner abstraction is the chapter support-function owner `supportFunction`
  on the dual pairing layer `(StrongDual ℝ E, E)`.
- `bridge/view`: the textbook notation `δ*(x* | B)` is exactly `supportFunction B xStar`, and the
  displayed supremum is the `sSup` bridge form.
- Primitive data vs derived API: the only primitive source object is the unit ball `B`; the norm
  formula is the main source-facing theorem for that owner, and the displayed supremum is a thin
  bridge back to the source notation.
- Ambient refinement: this owner statement uses only the continuous-dual pairing and norm bounds,
  so it is stated on arbitrary real normed spaces; the inner-product self-dual statement appears
  below as a specialization bridge.

Domain-style sampling used here:
- the project support-function specification theorem `supportFunction_def` and notation `δᵛ`;
- the Chapter 2 source-facing unit-closed-ball notation `B` with owner
  `Metric.closedBall (0 : E) 1`;
- mathlib's unit-ball membership lemma `mem_closedBall_zero_iff`;
- operator-norm upper bound `ContinuousLinearMap.le_opNorm`;
- strict approximation lemma `ContinuousLinearMap.exists_lt_apply_of_lt_opNorm`.

Layer target: `source-facing`; the main theorem is the owner-side support-function formula for the
chapter unit closed ball, and a companion theorem keeps the source's explicit supremum formula
visible.
-/

private theorem sSup_image_apply_unitClosedBall_eq_norm (xStar : StrongDual ℝ E) :
    sSup ((fun y : E ↦ xStar y) '' B) = ‖xStar‖ := by
  let S : Set ℝ := (fun y : E ↦ xStar y) '' B
  have hS_nonempty : S.Nonempty := by
    refine ⟨0, ⟨0, ?_, by simp⟩⟩
    simp
  have hS_bound : ∀ z ∈ S, z ≤ ‖xStar‖ := by
    rintro z ⟨y, hy, rfl⟩
    have hy_norm : ‖y‖ ≤ 1 := by
      simpa using (mem_closedBall_zero_iff.mp hy)
    calc
      xStar y ≤ ‖xStar y‖ := le_abs_self _
      _ ≤ ‖xStar‖ * ‖y‖ := xStar.le_opNorm y
      _ ≤ ‖xStar‖ * 1 := by gcongr
      _ = ‖xStar‖ := by ring
  have hS_bddAbove : BddAbove S := ⟨‖xStar‖, hS_bound⟩
  have hSup_le : sSup S ≤ ‖xStar‖ := by
    exact csSup_le hS_nonempty hS_bound
  have hNorm_le : ‖xStar‖ ≤ sSup S := by
    refine le_of_forall_lt ?_
    intro r hr
    obtain ⟨x, hx_norm, hx_apply⟩ := xStar.exists_lt_apply_of_lt_opNorm hr
    by_cases hx_nonneg : 0 ≤ xStar x
    · have hx_mem : xStar x ∈ S := by
        refine ⟨x, ?_, rfl⟩
        simpa [mem_closedBall_zero_iff] using hx_norm.le
      have hr_apply : r < xStar x := by
        simpa [abs_of_nonneg hx_nonneg] using hx_apply
      exact lt_of_lt_of_le hr_apply (le_csSup hS_bddAbove hx_mem)
    · have hx_neg : xStar x < 0 := lt_of_not_ge hx_nonneg
      have hx_mem : xStar (-x) ∈ S := by
        refine ⟨-x, ?_, rfl⟩
        simpa [mem_closedBall_zero_iff, norm_neg] using hx_norm.le
      have hr_apply : r < xStar (-x) := by
        simpa [abs_of_neg hx_neg] using hx_apply
      exact lt_of_lt_of_le hr_apply (le_csSup hS_bddAbove hx_mem)
  simpa [S] using (hSup_le.antisymm hNorm_le)

private theorem sSup_image_coe_withTopBot_eq_coe_sSup {S : Set ℝ}
    (hS_nonempty : S.Nonempty) (hS_bddAbove : BddAbove S) :
    sSup ((fun z : ℝ ↦ ((z : WithTopBot ℝ))) '' S) = (sSup S : ℝ) := by
  let SB : Set (WithBot ℝ) := ((fun z : ℝ ↦ ((z : WithBot ℝ))) '' S)
  have hSB_nonempty : SB.Nonempty := by
    rcases hS_nonempty with ⟨z, hz⟩
    exact ⟨(z : WithBot ℝ), ⟨z, hz, rfl⟩⟩
  have hSB_bddAbove : BddAbove SB := by
    rcases hS_bddAbove with ⟨u, hu⟩
    refine ⟨(u : WithBot ℝ), ?_⟩
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact (WithBot.coe_le_coe).2 (hu hx)
  have hcoe_bot :
      (sSup SB : WithBot ℝ) = (sSup S : ℝ) := by
    simpa [SB] using (WithBot.coe_sSup' (s := S) hS_nonempty hS_bddAbove).symm
  have hcoe_top :
      (sSup ((fun z : WithBot ℝ ↦ ((z : WithTopBot ℝ))) '' SB) : WithTopBot ℝ) =
        ((sSup SB : WithBot ℝ) : WithTopBot ℝ) := by
    simpa using (WithTop.coe_sSup' (s := SB) hSB_bddAbove).symm
  have himage :
      ((fun z : ℝ ↦ ((z : WithTopBot ℝ))) '' S) =
        ((fun z : WithBot ℝ ↦ ((z : WithTopBot ℝ))) '' SB) := by
    ext w
    constructor
    · intro hw
      rcases hw with ⟨x, hx, rfl⟩
      exact ⟨(x : WithBot ℝ), ⟨x, hx, rfl⟩, rfl⟩
    · intro hw
      rcases hw with ⟨z, hz, rfl⟩
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  calc
    sSup ((fun z : ℝ ↦ ((z : WithTopBot ℝ))) '' S) =
        sSup ((fun z : WithBot ℝ ↦ ((z : WithTopBot ℝ))) '' SB) := by
          simp [himage]
    _ = ((sSup SB : WithBot ℝ) : WithTopBot ℝ) := hcoe_top
    _ = (sSup S : ℝ) := by
      exact congrArg (fun t : WithBot ℝ ↦ (t : WithTopBot ℝ)) hcoe_bot

private theorem sSup_image_apply_unitClosedBall_eq_norm_withTopBot (xStar : StrongDual ℝ E) :
    sSup ((fun y : E ↦ ((xStar y : ℝ) : WithTopBot ℝ)) '' B) =
      (‖xStar‖ : WithTopBot ℝ) := by
  let S : Set ℝ := (fun y : E ↦ xStar y) '' B
  have hS_nonempty : S.Nonempty := by
    refine ⟨0, ⟨0, ?_, by simp⟩⟩
    simp
  have hS_bddAbove : BddAbove S := by
    refine ⟨‖xStar‖, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    have hy_norm : ‖y‖ ≤ 1 := by
      simpa using (mem_closedBall_zero_iff.mp hy)
    calc
      xStar y ≤ ‖xStar y‖ := le_abs_self _
      _ ≤ ‖xStar‖ * ‖y‖ := xStar.le_opNorm y
      _ ≤ ‖xStar‖ * 1 := by gcongr
      _ = ‖xStar‖ := by ring
  calc
    sSup ((fun y : E ↦ ((xStar y : ℝ) : WithTopBot ℝ)) '' B) =
        sSup ((fun z : ℝ ↦ ((z : WithTopBot ℝ))) '' S) := by
          simp [S, Set.image_image]
    _ = (sSup S : ℝ) :=
      sSup_image_coe_withTopBot_eq_coe_sSup hS_nonempty hS_bddAbove
    _ = (‖xStar‖ : WithTopBot ℝ) := by
      exact congrArg (fun t : ℝ ↦ (t : WithTopBot ℝ))
        (by simpa [S] using sSup_image_apply_unitClosedBall_eq_norm (xStar := xStar))

/-- Text 13.2.4 at the intrinsic dual-owner layer: for the unit closed ball
`B = {y | ‖y‖ ≤ 1}`, the support value is the operator norm of the dual vector. -/
theorem supportFunction_unitClosedBall_eq_norm (xStar : StrongDual ℝ E) :
    δᵛ(xStar | (B : Set E)) = (‖xStar‖ : WithTopBot ℝ) := by
  calc
    δᵛ(xStar | (B : Set E)) =
        sSup ((fun y : E ↦ (⟪xStar, y⟫ₚ : WithTopBot ℝ)) '' B) := by
          exact supportFunction_eq_sSup_image (L := WithTopBot ℝ) (C := (B : Set E)) (x := xStar)
    _ = sSup ((fun y : E ↦ ((xStar y : ℝ) : WithTopBot ℝ)) '' B) := by
          rfl
    _ = (‖xStar‖ : WithTopBot ℝ) := by
          simpa using sSup_image_apply_unitClosedBall_eq_norm_withTopBot (xStar := xStar)

/-- Owner-level function form of Text 13.2.4 on the dual side:
the support-function map of the unit closed ball is the norm map. -/
theorem supportFunction_unitClosedBall_eq_norm_fun :
    (δᵛ(· | (B : Set E)) : StrongDual ℝ E → WithTopBot ℝ) =
      (fun xStar : StrongDual ℝ E ↦ (‖xStar‖ : WithTopBot ℝ)) := by
  funext xStar
  simpa using supportFunction_unitClosedBall_eq_norm (xStar := xStar)

/-- The explicit supremum formula from Text 13.2.4 on the intrinsic dual-owner layer,
in the chapter-canonical codomain `WithTopBot ℝ`. -/
theorem sSup_image_unitClosedBall_eq_norm (xStar : StrongDual ℝ E) :
    sSup ((fun y : E ↦ (⟪xStar, y⟫ₚ : WithTopBot ℝ)) '' B) =
      (‖xStar‖ : WithTopBot ℝ) := by
  calc
    sSup ((fun y : E ↦ (⟪xStar, y⟫ₚ : WithTopBot ℝ)) '' B) =
        sSup ((fun y : E ↦ ((xStar y : ℝ) : WithTopBot ℝ)) '' B) := by
          rfl
    _ = (‖xStar‖ : WithTopBot ℝ) := by
          simpa using sSup_image_apply_unitClosedBall_eq_norm_withTopBot (xStar := xStar)

/-- Real-valued bridge form of Text 13.2.4's explicit supremum identity. -/
theorem sSup_image_unitClosedBall_eq_norm_real (xStar : StrongDual ℝ E) :
    sSup ((fun y : E ↦ (⟪xStar, y⟫ₚ : ℝ)) '' B) = ‖xStar‖ := by
  calc
    sSup ((fun y : E ↦ (⟪xStar, y⟫ₚ : ℝ)) '' B) =
        sSup ((fun y : E ↦ xStar y) '' B) := by
          rfl
    _ = ‖xStar‖ := by
          simpa using sSup_image_apply_unitClosedBall_eq_norm (xStar := xStar)

end Dual

section InnerProduct

open Metric
open scoped RealInnerProductSpace Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Text 13.2.4, inner-product self-dual specialization: for the unit closed ball
`B = {y | ‖y‖ ≤ 1}` in a real inner-product space, the support value `δ*(x | B)` is the norm of
`x`. -/
theorem supportFunction_unitClosedBall_eq_norm_inner (x : E) :
    δᵛ(x | (B : Set E)) = (‖x‖ : WithTopBot ℝ) := by
  let xStar : StrongDual ℝ E := (innerSL ℝ) x
  have hpair_apply :
      (fun y : E ↦ (⟪x, y⟫ₚ : WithTopBot ℝ)) =
        (fun y : E ↦ ((xStar y : ℝ) : WithTopBot ℝ)) := by
    funext y
    change (((innerSL ℝ x) y : ℝ) : WithTopBot ℝ) =
        (((xStar y : ℝ) : WithTopBot ℝ))
    simp [xStar]
  calc
    δᵛ(x | (B : Set E)) =
        sSup ((fun y : E ↦ (⟪x, y⟫ₚ : WithTopBot ℝ)) '' B) :=
      supportFunction_eq_sSup_image (L := WithTopBot ℝ) (C := (B : Set E)) (x := x)
    _ = sSup ((fun y : E ↦ ((xStar y : ℝ) : WithTopBot ℝ)) '' B) := by
      simp [hpair_apply]
    _ = δᵛ(xStar | (B : Set E)) :=
      (supportFunction_eq_sSup_image (L := WithTopBot ℝ) (C := (B : Set E)) (x := xStar)).symm
    _ = (‖xStar‖ : WithTopBot ℝ) := supportFunction_unitClosedBall_eq_norm (xStar := xStar)
    _ = (‖x‖ : WithTopBot ℝ) := by
      simp [xStar, innerSL_apply_norm]

/-- Owner-level function form of Text 13.2.4 in the inner-product self-dual specialization:
the support-function map of the unit closed ball is the norm map. -/
theorem supportFunction_unitClosedBall_eq_norm_inner_fun :
    (δᵛ(· | (B : Set E)) : E → WithTopBot ℝ) =
      (fun x : E ↦ (‖x‖ : WithTopBot ℝ)) := by
  funext x
  simpa using supportFunction_unitClosedBall_eq_norm_inner (x := x)

/-- The explicit supremum formula from Text 13.2.4 is the unit-closed-ball specialization of
`supportFunction_def` together with `supportFunction_unitClosedBall_eq_norm_inner`. -/
-- Proof sketch: rewrite the displayed supremum by `supportFunction_def`, then apply
-- `supportFunction_unitClosedBall_eq_norm_inner`.
theorem sSup_image_inner_unitClosedBall_eq_norm (x : E) :
    sSup ((fun y ↦ (⟪x, y⟫ : WithTopBot ℝ)) '' B) = (‖x‖ : WithTopBot ℝ) := by
  calc
    sSup ((fun y ↦ (⟪x, y⟫ : WithTopBot ℝ)) '' B) = δᵛ(x | (B : Set E)) :=
      (supportFunction_eq_sSup_image (L := WithTopBot ℝ) (C := (B : Set E)) (x := x)).symm
    _ = (‖x‖ : WithTopBot ℝ) := supportFunction_unitClosedBall_eq_norm_inner (x := x)

end InnerProduct
