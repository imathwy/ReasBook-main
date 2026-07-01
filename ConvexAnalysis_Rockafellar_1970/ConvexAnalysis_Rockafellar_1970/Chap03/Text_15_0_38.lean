import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_37

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise

section

variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the text identifies the `α`-sublevel set of the obverse `g = obverse f` with
  both the unit sublevel set of the scaled perspective `f_α` and the homothetic image
  `α • {x | f x ≤ α⁻¹}`.
- `core/canonical`: the owner API is the chapter-level source-facing trio
  `obverse`, `Function.rightScalarMul`, and the standing-hypothesis class
  `Function.IsNonnegativeClosedConvexZero`, imported upstream from `Text_15_0_31`.
- `bridge/view`: the first clause is now a direct specialization of the existing comparison
  theorem from `Text_15_0_37` at the unit scalar, under the standing Chapter 15 assumptions,
  while the second clause rewrites that unit sublevel set as a pointwise scalar multiple of an
  ordinary sublevel set of `f`.

Domain-style sampling used here:
- `obverse`;
- `rightScalarMul`;
- `perspectiveScale_le_iff_obverse_perspectiveScale_le`;
- `rightScalarMul_one`;
- `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos`;
- `Set.mem_smul_set_iff_inv_smul_mem₀`.

Layer target: `source-facing`, split into the two atomic equalities displayed in the source.
Ambient minimization: the first statement uses the intrinsic Chapter 15 owner layer
`[TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]`, while the second only needs the scalar
action laws required by the positive right scalar multiple formula and the homothetic-set rewrite,
namely `[MulAction ℝ E]`. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the source
presentation on `R^n`.
-/

-- Proof sketch: specialize the comparison theorem from `Text_15_0_37` to the unit scalar `μ = 1`.
-- The resulting right-hand side is the unit right scalar multiple of `obverse f` evaluated at
-- `x`, bounded by `α`, which reduces to
-- `obverse f x ≤ α` by the owner theorem `rightScalarMul_one`.
/-- Text 15.0.38 (1): for every positive scalar `α`, the `α`-sublevel set of the obverse
`g = obverse f` is exactly the unit sublevel set of the scaled perspective `f_α`, provided `f`
satisfies the standing Chapter 15 assumptions. Specializing `E` to
`EuclideanSpace ℝ (Fin n)` recovers the source statement on `R^n`. -/
theorem obverse_sublevelSet_eq_perspectiveScale_unitSublevelSet
    (f : E → EReal) (hf : f.IsNonnegativeClosedConvexZero) (α : NNRealˣ) :
    {x : E | obverse f x ≤ ((α : ℝ) : EReal)} =
      {x : E | ((α : NNReal) •ʳ f) x ≤ (1 : EReal)} := by
  ext x
  have hone : ((1 : NNReal) •ʳ obverse f) = obverse f :=
    (rightScalarMul_one (obverse f) : ((1 : NNReal) •ʳ obverse f) = obverse f)
  simpa [hone] using (perspectiveScale_le_iff_obverse_perspectiveScale_le f hf α 1 x).symm

end

section

variable {E : Type*} [MulAction ℝ E]

-- Proof sketch: unfold the positive right scalar multiple; the inequality
-- `α * f (α⁻¹ • x) ≤ 1` is equivalent to
-- `f (α⁻¹ • x) ≤ α⁻¹`. Writing `u = α⁻¹ • x` turns the unit sublevel set of `f_α` into the image
-- of `{u | f u ≤ α⁻¹}` under multiplication by `α`, i.e. into `α • {u | f u ≤ α⁻¹}`.
/-- Text 15.0.38 (2): for every positive scalar `α`, the unit sublevel set of the scaled
perspective `f_α` is the homothetic image by `α` of the `α⁻¹`-sublevel set of `f`. Specializing
`E` to `EuclideanSpace ℝ (Fin n)` recovers the source statement on `R^n`. -/
theorem perspectiveScale_unitSublevelSet_eq_smul_sublevelSet
    (f : E → EReal) (α : NNRealˣ) :
    {x : E | ((α : NNReal) •ʳ f) x ≤ (1 : EReal)} =
      (α : ℝ) • {x : E | f x ≤ (((α⁻¹ : NNRealˣ) : ℝ) : EReal)} := by
  ext x
  let f' : E → WithBotTop ℝ := f
  have hαreal : 0 < (α : ℝ) := by
    exact_mod_cast (show 0 < (α : NNReal) from pos_iff_ne_zero.mpr (Units.ne_zero α))
  have hα : (0 : EReal) < (α : ℝ) := by
    exact_mod_cast (show 0 < (α : NNReal) from pos_iff_ne_zero.mpr (Units.ne_zero α))
  have hα0 : (α : ℝ) ≠ 0 := by
    exact_mod_cast (Units.ne_zero α)
  have hαTop : ((α : ℝ) : EReal) ≠ ⊤ := by
    simp
  have hαnn : (⟨(α : ℝ), hαreal.le⟩ : NNReal) = (α : NNReal) := by
    ext
    rfl
  have hright :
      ((⟨(α : ℝ), hαreal.le⟩ : NNReal) •ʳ f') x =
        (((α : ℝ) : WithBotTop ℝ)) * f' (((α : ℝ)⁻¹) • x) := by
    simpa [f'] using rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos f' hαreal x
  constructor <;> intro hx
  · exact
      (Set.mem_smul_set_iff_inv_smul_mem₀ hα0
        {x : E | f x ≤ (((α⁻¹ : NNRealˣ) : ℝ) : EReal)} x).2 <| by
      change ((α : NNReal) •ʳ f) x ≤ (1 : EReal) at hx
      rw [← hαnn] at hx
      change ((⟨(α : ℝ), hαreal.le⟩ : NNReal) •ʳ f') x ≤ (1 : WithBotTop ℝ) at hx
      rw [hright] at hx
      have hx' : f' (((α : ℝ)⁻¹) • x) * (((α : ℝ) : WithBotTop ℝ)) ≤ (1 : WithBotTop ℝ) := by
        rwa [f', mul_comm] at hx
      have hx'' :
          f' (((α : ℝ)⁻¹) • x) ≤
            (1 : WithBotTop ℝ) / (((α : ℝ) : WithBotTop ℝ)) :=
        (EReal.le_div_iff_mul_le hα hαTop).mpr hx'
      simpa [f', div_eq_mul_inv, EReal.coe_inv, mul_comm, mul_left_comm, mul_assoc] using hx''
  · have hx' :=
      (Set.mem_smul_set_iff_inv_smul_mem₀ hα0
        {x : E | f x ≤ (((α⁻¹ : NNRealˣ) : ℝ) : EReal)} x).1 hx
    change ((α : NNReal) •ʳ f) x ≤ (1 : EReal)
    rw [← hαnn]
    change ((⟨(α : ℝ), hαreal.le⟩ : NNReal) •ʳ f') x ≤ (1 : WithBotTop ℝ)
    rw [hright]
    have hx'' :
        f' (((α : ℝ)⁻¹) • x) ≤
          (1 : WithBotTop ℝ) / (((α : ℝ) : WithBotTop ℝ)) := by
      simpa [f', div_eq_mul_inv, EReal.coe_inv, mul_comm, mul_left_comm, mul_assoc] using hx'
    have hx''' :
        f' (((α : ℝ)⁻¹) • x) * (((α : ℝ) : WithBotTop ℝ)) ≤ (1 : WithBotTop ℝ) :=
      (EReal.le_div_iff_mul_le hα hαTop).mp hx''
    rwa [f', mul_comm]

end
