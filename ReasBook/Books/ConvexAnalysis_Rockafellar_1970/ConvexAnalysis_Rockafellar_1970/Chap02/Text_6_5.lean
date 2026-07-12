import Mathlib
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_3

-- Declarations for this item will be appended below by the statement pipeline.

open Metric
open scoped Pointwise Rockafellar

section

variable {𝕜 : Type*} [NormedDivisionRing 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]

/-- Canonical scalar-generic bridge: a closed ball of radius `‖c‖` is a translate of a scalar
multiple of the unit closed ball owner `B`. -/
theorem closedBall_eq_add_smul_unitClosedBall_of_ne_zero (a : E) {c : 𝕜} (hc : c ≠ 0) :
    closedBall a ‖c‖ = a +ᵥ (c • (B : Set E)) := by
  have hsmul :
      closedBall (0 : E) ‖c‖ = c • (B : Set E) := by
    ext x
    constructor
    · intro hx
      refine ⟨c⁻¹ • x, ?_, by simp [smul_smul, hc]⟩
      rw [Metric.mem_closedBall] at hx ⊢
      have hdist : dist x (0 : E) = ‖c‖ * dist (c⁻¹ • x) (0 : E) := by
        simpa [smul_smul, hc] using (dist_smul₀ c (c⁻¹ • x) (0 : E))
      have hmul : ‖c‖ * dist (c⁻¹ • x) (0 : E) ≤ ‖c‖ * (1 : ℝ) := by
        calc
          ‖c‖ * dist (c⁻¹ • x) (0 : E) = dist x (0 : E) := hdist.symm
          _ ≤ ‖c‖ := hx
          _ = ‖c‖ * (1 : ℝ) := by simp
      have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
      have hdist_nonneg : 0 ≤ dist (c⁻¹ • x) (0 : E) := dist_nonneg
      nlinarith
    · rintro ⟨y, hy, rfl⟩
      rw [Metric.mem_closedBall] at hy ⊢
      calc
        dist (c • y) (0 : E) = ‖c‖ * dist y (0 : E) := by
          simpa using (dist_smul₀ c y (0 : E))
        _ ≤ ‖c‖ * (1 : ℝ) := by gcongr
        _ = ‖c‖ := by simp
  calc
    closedBall a ‖c‖ = a +ᵥ closedBall (0 : E) ‖c‖ := by
      exact (vadd_closedBall_zero (x := a) (δ := ‖c‖)).symm
    _ = a +ᵥ (c • (B : Set E)) := by rw [hsmul]

/-- Canonical scalar-generic bridge with intrinsic invertibility witness:
for a unit scalar `u : 𝕜ˣ`, the closed ball of radius `‖u‖` is `a + u • B`. -/
theorem closedBall_eq_add_smul_unitClosedBall_unit (a : E) (u : 𝕜ˣ) :
    closedBall a ‖(u : 𝕜)‖ = a +ᵥ ((u : 𝕜) • (B : Set E)) := by
  simpa using
    (closedBall_eq_add_smul_unitClosedBall_of_ne_zero
      (a := a) (c := (u : 𝕜)) u.ne_zero)

/-- Canonical scalar-generic owner bridge: for any scalar `c`, the closed ball of radius `‖c‖`
is the translate-dilate `a + c • B`. The endpoint `c = 0` needs separation (`T1Space`) so that
`closedBall a 0 = {a}`. -/
theorem closedBall_eq_add_smul_unitClosedBall [T1Space E] (a : E) (c : 𝕜) :
    closedBall a ‖c‖ = a +ᵥ (c • (B : Set E)) := by
  by_cases hc : c = 0
  · subst hc
    ext x
    simp [Metric.closedBall_zero', Set.mem_vadd_set, eq_comm]
  · exact closedBall_eq_add_smul_unitClosedBall_of_ne_zero (a := a) (c := c) hc

end

section

variable {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [NormSMulClass ℝ E]

/-
Source/core/bridge triage:
- `source-facing`: Text 6.5 describes the closed ball centered at `a` with radius `ε` as both the
  translated norm-sublevel set `{a + y | ‖y‖ ≤ ε}` and the translate/dilate `a + ε B` of the unit
  ball.
- `core/canonical`: the owner abstraction is the metric closed ball `closedBall a ε`.
- `bridge/view`: the intrinsic translation presentations
  `a +ᵥ (ε • B)` and `a +ᵥ {y : E | ‖y‖ ≤ ε}` are bridge views of the same owner object.
- Primitive data vs derived API: the primitive inputs are the center `a` and radius `ε`; the
  translated-unit-ball and translated-sublevel descriptions are derived API.
- Domain-style sampling: `closedBall`, `Metric.mem_closedBall`, `mem_closedBall_zero_iff`,
  `smul_closedBall'`, `vadd_closedBall_zero`, and `Metric.closedBall_zero'`.
- Layer target: `bridge/view`, keeping `closedBall` as owner and expressing the textbook forms as
  thin companion theorems.
-/

/-- Text 6.5, owner bridge for positive radii: a closed ball is the translate and dilation of the
unit closed ball, written in pointwise-set form. -/
theorem closedBall_eq_add_smul_unitClosedBall_of_pos (a : E) {ε : ℝ} (hε : 0 < ε) :
    closedBall a ε = a +ᵥ (ε • (B : Set E)) := by
  simpa [Real.norm_of_nonneg hε.le] using
    (closedBall_eq_add_smul_unitClosedBall_of_ne_zero (a := a) (c := ε) hε.ne')

/-- Text 6.5, owner bridge: a closed ball is the translate and dilation of the unit closed ball,
written in pointwise-set form. The `ε = 0` endpoint needs separation (`T1Space`) so that
`closedBall a 0 = {a}`. -/
theorem closedBall_eq_add_smul_unitClosedBall_of_nonneg [T1Space E] (a : E) {ε : ℝ} (hε : 0 ≤ ε) :
    closedBall a ε = a +ᵥ (ε • (B : Set E)) := by
  simpa [Real.norm_of_nonneg hε] using
    (closedBall_eq_add_smul_unitClosedBall (a := a) (c := ε))

/- The metric set-builder presentation `closedBall a ε = {x | dist x a ≤ ε}` is already the
canonical owner API `Metric.mem_closedBall`, so no parallel wrapper theorem is introduced here. -/
recall Metric.mem_closedBall

end

section

variable {E : Type*} [PseudoMetricSpace E] [AddGroup E] [IsIsometricVAdd E E]

/-- A closed ball is the translate of the zero-centered closed ball by `a`. -/
theorem closedBall_eq_vadd_closedBall_zero (a : E) (ε : ℝ) :
    closedBall a ε = a +ᵥ closedBall (0 : E) ε := by
  calc
    closedBall a ε = closedBall ((IsometryEquiv.addLeft a) 0) ε := by
      simp
    _ = ((IsometryEquiv.addLeft a : E → E) '' closedBall (0 : E) ε) := by
      exact ((IsometryEquiv.addLeft a).image_closedBall (0 : E) ε).symm
    _ = a +ᵥ closedBall (0 : E) ε := by
      rfl

end

section

variable {E : Type*} [SeminormedAddGroup E]

/-- A closed ball is the translate by `a` of the norm sublevel set `{y | ‖y‖ ≤ ε}`. -/
-- Proof sketch: this is the translation-isometry owner theorem
-- `closedBall_eq_vadd_closedBall_zero`, with the zero-centered closed ball identified with
-- its canonical norm-sublevel presentation via `mem_closedBall_zero_iff`.
theorem closedBall_eq_vadd_norm_sublevel (a : E) (ε : ℝ) :
    closedBall a ε = a +ᵥ {y : E | ‖y‖ ≤ ε} := by
  rw [closedBall_eq_vadd_closedBall_zero (a := a) (ε := ε)]
  congr 1
  ext y
  simp

end
