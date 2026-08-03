import Mathlib
import BauschkeLean.Chap01.Definition_1_8
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Example_9_48
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap09.Proposition_9_42
import BauschkeLean.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

namespace ERealFunction

/-- The source-facing function from Example 11.25. The `source-facing` owner is this two-variable
relative-entropy formula, while the `core/canonical` primitive data is the Chapter 9 closed
perspective of `closed_relative_entropy_generator`; the only `bridge/view` layer is the coordinate
swap `(ξ₁, ξ₂) ↦ (ξ₂, ξ₁)` together with the affine correction `ξ₂ - ξ₁`. -/
noncomputable def closedScalarRelativeEntropy : ℝ × ℝ → Set.Ioi (⊥ : EReal) :=
  fun p ↦
    let hdom := closed_relative_entropy_generator_mem_gammaZero.2.nonempty
    ⟨(closedPerspective closed_relative_entropy_generator hdom (p.2, p.1) : EReal) +
        (p.2 - p.1 : ℝ),
      bot_lt_iff_ne_bot.mpr <|
        (EReal.add_ne_bot_iff).2
          ⟨(closedPerspective closed_relative_entropy_generator hdom (p.2, p.1)).2.ne',
            EReal.coe_ne_bot _⟩⟩

/-- The source-facing scalar relative entropy is the Chapter 9 closed perspective of the closed
relative-entropy generator, viewed on swapped coordinates and corrected by the affine term
`ξ₂ - ξ₁`. -/
@[simp] theorem closedScalarRelativeEntropy_coe (p : ℝ × ℝ) :
    (closedScalarRelativeEntropy p : EReal) =
      (closedPerspective closed_relative_entropy_generator
        closed_relative_entropy_generator_mem_gammaZero.2.nonempty (p.2, p.1) : EReal) +
        (p.2 - p.1 : ℝ) := by
  simp [closedScalarRelativeEntropy]

local notation "f" => closedScalarRelativeEntropy.asEReal

/-- Helper for Example 11 25: the recession function of the closed relative-entropy generator
vanishes at the origin and equals `+∞` on every nonzero direction. -/
private theorem recession_closed_relative_entropy_generator_apply (t : ℝ) :
    (recessionFunction closed_relative_entropy_generator
      closed_relative_entropy_generator_mem_gammaZero.2.nonempty t : EReal) =
      if t = 0 then 0 else ⊤ :=
by
  -- Evaluate the supercoercive recession formula at `t` and then simplify the singleton indicator.
  have ht :=
    congrFun
      (recessionFunction_eq_indicator_singleton_zero_of_supercoercive
        closed_relative_entropy_generator_mem_gammaZero
        closed_relative_entropy_generator_supercoercive) t
  by_cases hzero : t = 0
  · subst hzero
    simpa using ht
  · simpa [Set.indicator, hzero] using ht

/-- Helper for Example 11 25: on the positive orthant, the logarithmic branch of the scalar
relative entropy is the textbook `ξ₂ * klFun (ξ₁ / ξ₂)` normal form. -/
private theorem closedScalarRelativeEntropy_pos_eq_mul_klFun {ξ₁ ξ₂ : ℝ}
    (_hξ₁ : 0 < ξ₁) (hξ₂ : 0 < ξ₂) :
    ξ₁ * Real.log (ξ₁ / ξ₂) - ξ₁ + ξ₂ =
      ξ₂ * InformationTheory.klFun (ξ₁ / ξ₂) := by
  -- Expand `klFun` and collapse the reciprocal factor `ξ₂ * (ξ₁ / ξ₂)` back to `ξ₁`.
  rw [InformationTheory.klFun_apply]
  calc
    ξ₁ * Real.log (ξ₁ / ξ₂) - ξ₁ + ξ₂
        = ξ₂ * ((ξ₁ / ξ₂) * Real.log (ξ₁ / ξ₂)) + (ξ₂ - ξ₁) := by
            field_simp [hξ₂.ne']
            ring
    _ = ξ₂ * (((ξ₁ / ξ₂) * Real.log (ξ₁ / ξ₂)) + 1 - (ξ₁ / ξ₂)) := by
          field_simp [hξ₂.ne']
          ring

/- Example 11.25: evaluating `closedScalarRelativeEntropy` gives the three-branch textbook formula:
the logarithmic expression on the positive orthant, the vertical branch `{0} × ℝ₊`, and `+∞`
otherwise. -/
@[simp] theorem closedScalarRelativeEntropy_apply (ξ₁ ξ₂ : ℝ) :
    (closedScalarRelativeEntropy (ξ₁, ξ₂) : EReal) =
      if 0 < ξ₁ ∧ 0 < ξ₂ then
        ((ξ₁ * Real.log (ξ₁ / ξ₂) - ξ₁ + ξ₂ : ℝ) : EReal)
      else if ξ₁ = 0 ∧ 0 ≤ ξ₂ then
        ξ₂
      else
        ⊤ := by
  -- Route correction: the source proof is governed by the closed-perspective height `ξ₂`, so
  -- split on `ξ₂ = 0`, `0 < ξ₂`, and `ξ₂ < 0` before inspecting the numerator `ξ₁`.
  rw [closedScalarRelativeEntropy_coe, closedPerspective_coe]
  by_cases hξ₂0 : ξ₂ = 0
  · -- On the zero-height slice, the closed perspective is the recession function.
    rw [hξ₂0, closedPerspectiveEReal_apply_zero, recession_closed_relative_entropy_generator_apply]
    by_cases hξ₁0 : ξ₁ = 0
    · subst hξ₁0
      simp
    · simp [hξ₁0]
  · by_cases hξ₂_pos : 0 < ξ₂
    · -- Positive height reduces the closed perspective to the ordinary perspective.
      rw [closedPerspectiveEReal_apply_of_ne_zero
        (φ := closed_relative_entropy_generator)
        (hdom := closed_relative_entropy_generator_mem_gammaZero.2.nonempty) hξ₂0,
        perspective_apply_of_pos (fun t : ℝ ↦ (closed_relative_entropy_generator t : EReal))
          hξ₂_pos]
      have hratio : ξ₂⁻¹ • ξ₁ = ξ₁ / ξ₂ := by
        simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
      rw [hratio]
      by_cases hξ₁_pos : 0 < ξ₁
      · -- On the positive orthant, the generator contributes the logarithmic branch.
        rw [closed_relative_entropy_generator_apply_of_pos (div_pos hξ₁_pos hξ₂_pos)]
        have hreal :
            ξ₂ * ((ξ₁ / ξ₂) * Real.log (ξ₁ / ξ₂)) + (ξ₂ - ξ₁) =
              ξ₁ * Real.log (ξ₁ / ξ₂) - ξ₁ + ξ₂ := by
          field_simp [hξ₂_pos.ne']
          ring
        calc
          (ξ₂ : EReal) * (((ξ₁ / ξ₂) * Real.log (ξ₁ / ξ₂) : ℝ) : EReal) +
              ((ξ₂ - ξ₁ : ℝ) : EReal)
              = ((ξ₂ * ((ξ₁ / ξ₂) * Real.log (ξ₁ / ξ₂)) + (ξ₂ - ξ₁) : ℝ) : EReal) := by
                  rw [← EReal.coe_mul, ← EReal.coe_add]
          _ = ((ξ₁ * Real.log (ξ₁ / ξ₂) - ξ₁ + ξ₂ : ℝ) : EReal) := by
                exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
          _ = if 0 < ξ₁ ∧ 0 < ξ₂ then
                ((ξ₁ * Real.log (ξ₁ / ξ₂) - ξ₁ + ξ₂ : ℝ) : EReal)
              else if ξ₁ = 0 ∧ 0 ≤ ξ₂ then
                ξ₂
              else
                ⊤ := by
                  simp [hξ₁_pos, hξ₂_pos]
      · by_cases hξ₁0 : ξ₁ = 0
        · -- With zero numerator and positive height, only the vertical branch survives.
          subst hξ₁0
          rw [zero_div, closed_relative_entropy_generator_apply_zero]
          simp [hξ₂_pos, hξ₂_pos.le]
        · -- A negative numerator sends the generator to `⊤`, so the whole value is `⊤`.
          have hξ₁_neg : ξ₁ < 0 := lt_of_le_of_ne (le_of_not_gt hξ₁_pos) hξ₁0
          rw [
            closed_relative_entropy_generator_apply_of_neg
              (div_neg_of_neg_of_pos hξ₁_neg hξ₂_pos),
            EReal.coe_mul_top_of_pos hξ₂_pos
          ]
          simpa [hξ₁_pos, hξ₁0, hξ₂_pos] using
            (EReal.top_add_of_ne_bot (EReal.coe_ne_bot (ξ₂ - ξ₁)))
    · -- Negative height falls on the `+∞` branch of the perspective.
      rw [closedPerspectiveEReal_apply_of_ne_zero
        (φ := closed_relative_entropy_generator)
        (hdom := closed_relative_entropy_generator_mem_gammaZero.2.nonempty) hξ₂0,
        perspective_apply_of_nonpos (fun t : ℝ ↦ (closed_relative_entropy_generator t : EReal))
          (le_of_not_gt hξ₂_pos)]
      have hξ₂_neg : ξ₂ < 0 := lt_of_le_of_ne (le_of_not_gt hξ₂_pos) hξ₂0
      simpa [hξ₂_pos, not_le_of_gt hξ₂_neg] using
        (EReal.top_add_of_ne_bot (EReal.coe_ne_bot (ξ₂ - ξ₁)))

/- On the strictly positive orthant, `closedScalarRelativeEntropy` is
`ξ₁ log (ξ₁ / ξ₂) - ξ₁ + ξ₂`. -/
-- Proof sketch: this is the positive branch of `closedScalarRelativeEntropy_apply`.
theorem closedScalarRelativeEntropy_apply_of_pos {ξ₁ ξ₂ : ℝ} (hξ₁ : 0 < ξ₁) (hξ₂ : 0 < ξ₂) :
    (closedScalarRelativeEntropy (ξ₁, ξ₂) : EReal) =
      ((ξ₁ * Real.log (ξ₁ / ξ₂) - ξ₁ + ξ₂ : ℝ) : EReal) := by
  rw [closedScalarRelativeEntropy_apply, if_pos ⟨hξ₁, hξ₂⟩]

/- On the vertical half-line `{0} × ℝ₊`, `closedScalarRelativeEntropy` is the second coordinate. -/
-- Proof sketch: this is the second branch of `closedScalarRelativeEntropy_apply`.
theorem closedScalarRelativeEntropy_apply_zero_left {ξ₂ : ℝ} (hξ₂ : 0 ≤ ξ₂) :
    (closedScalarRelativeEntropy (0, ξ₂) : EReal) = ξ₂ := by
  rw [closedScalarRelativeEntropy_apply, if_neg (by simp), if_pos ⟨rfl, hξ₂⟩]

/- Away from the positive orthant and the branch `{0} × ℝ₊`, `closedScalarRelativeEntropy` is
`+∞`. -/
-- Proof sketch: this is the final branch of `closedScalarRelativeEntropy_apply`.
theorem closedScalarRelativeEntropy_apply_of_otherwise {ξ₁ ξ₂ : ℝ}
    (hpos : ¬ (0 < ξ₁ ∧ 0 < ξ₂)) (hzero : ¬ (ξ₁ = 0 ∧ 0 ≤ ξ₂)) :
    (closedScalarRelativeEntropy (ξ₁, ξ₂) : EReal) = ⊤ := by
  rw [closedScalarRelativeEntropy_apply, if_neg hpos, if_neg hzero]

/- The source-facing scalar relative entropy belongs to `Γ₀(ℝ × ℝ)`. -/
-- Proof sketch: realize the textbook piecewise formula as the closed perspective of the
-- Chapter 9 closed relative-entropy generator, then add the affine correction `ξ₂ - ξ₁`.
/-- Helper for Example 11 25: swapping the coordinates of the closed perspective preserves its
`Γ₀` membership. -/
private theorem swapped_closedPerspective_mem_gammaZero :
    (closedPerspective closed_relative_entropy_generator
      closed_relative_entropy_generator_mem_gammaZero.2.nonempty ∘
        ContinuousLinearEquiv.prodComm ℝ ℝ ℝ) ∈ Γ₀(ℝ × ℝ) := by
  -- Precomposition by the coordinate-swap equivalence preserves the Chapter 9 `Γ₀` owner.
  let g :=
    closedPerspective closed_relative_entropy_generator
      closed_relative_entropy_generator_mem_gammaZero.2.nonempty
  have hg : g ∈ Γ₀(ℝ × ℝ) := by
    simpa [g] using
      closedPerspective_mem_gammaZero closed_relative_entropy_generator
        closed_relative_entropy_generator_mem_gammaZero
  simpa [g, Function.comp] using
    mem_gammaZero_comp_continuousLinearEquiv hg
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)

/-- Helper for Example 11 25: the affine correction `p ↦ p.2 - p.1`, viewed in `EReal`, belongs
to `Γ(ℝ × ℝ)`. -/
private theorem affine_difference_mem_gamma :
    (fun p : ℝ × ℝ ↦ ((p.2 - p.1 : ℝ) : EReal)) ∈ Γ(ℝ × ℝ) := by
  rw [mem_gamma_iff]
  constructor
  · intro x y α _hα0 _hα1
    -- Affine functions satisfy Jensen's inequality with equality.
    have hformula :
        (α • x + (1 - α) • y).2 - (α • x + (1 - α) • y).1 =
          α * (x.2 - x.1) + (1 - α) * (y.2 - y.1) := by
      rcases x with ⟨x₁, x₂⟩
      rcases y with ⟨y₁, y₂⟩
      simp
      ring
    have hformulaE :
        ((((α • x + (1 - α) • y).2 - (α • x + (1 - α) • y).1 : ℝ) : EReal)) =
          (α : EReal) * (((x.2 - x.1 : ℝ) : EReal)) +
            (1 - α : EReal) * (((y.2 - y.1 : ℝ) : EReal)) := by
      rw [show (1 - (α : EReal)) = (((1 - α : ℝ) : EReal)) by norm_num,
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      exact congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hformula
    simpa [smul_eq_mul] using le_of_eq hformulaE
  · -- Continuity of the affine map yields lower semicontinuity after coercion to `EReal`.
    have hcont : Continuous fun p : ℝ × ℝ ↦ p.2 - p.1 := by
      simpa using (continuous_snd.sub continuous_fst)
    simpa [Function.comp] using (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous

/-- Helper for Example 11 25: the affine correction belongs to `Γ₀(ℝ × ℝ)` after the canonical
`toEReal` packaging. -/
private theorem affine_difference_toEReal_mem_gammaZero :
    (fun p : ℝ × ℝ ↦ p.2 - p.1).toEReal ∈ Γ₀(ℝ × ℝ) := by
  -- Package the everywhere-finite affine map through the standard real-to-`EReal` bridge.
  exact toEReal_mem_gammaZero_of_mem_gamma affine_difference_mem_gamma

/-- Helper for Example 11 25: the source-facing owner is exactly the pointwise sum of the swapped
closed perspective and the affine correction. -/
private theorem closedScalarRelativeEntropy_eq_swapped_closedPerspective_add_affine :
    closedScalarRelativeEntropy =
      (closedPerspective closed_relative_entropy_generator
        closed_relative_entropy_generator_mem_gammaZero.2.nonempty ∘
          ContinuousLinearEquiv.prodComm ℝ ℝ ℝ) +
        (fun p : ℝ × ℝ ↦ p.2 - p.1).toEReal := by
  funext p
  apply Subtype.ext
  -- Rewrite both sides to the same `EReal` expression pointwise.
  rcases p with ⟨x, y⟩
  simp [closedScalarRelativeEntropy_coe, Function.comp]

theorem closedScalarRelativeEntropy_mem_gammaZero :
    closedScalarRelativeEntropy ∈ Γ₀(ℝ × ℝ) := by
  -- Route correction: instead of searching for an ad hoc `Γ₀` wrapper for the whole formula,
  -- package the swapped perspective and the affine correction separately, then add them.
  have hsum :
      ((closedPerspective closed_relative_entropy_generator
        closed_relative_entropy_generator_mem_gammaZero.2.nonempty ∘
          ContinuousLinearEquiv.prodComm ℝ ℝ ℝ) +
        (fun p : ℝ × ℝ ↦ p.2 - p.1).toEReal) ∈ Γ₀(ℝ × ℝ) := by
    have hdom :
        (effectiveDomain
            (closedPerspective closed_relative_entropy_generator
              closed_relative_entropy_generator_mem_gammaZero.2.nonempty ∘
                ContinuousLinearEquiv.prodComm ℝ ℝ ℝ) ∩
          effectiveDomain ((fun p : ℝ × ℝ ↦ p.2 - p.1).toEReal)).Nonempty := by
      have hone_mem : ((1 : ℝ), (1 : ℝ)) ∈ effectiveDomain closedScalarRelativeEntropy := by
        rw [mem_effectiveDomain_iff]
        -- The positive branch shows the source-facing function is finite at `(1, 1)`.
        have hone_value : (closedScalarRelativeEntropy (1, 1) : EReal) = 0 := by
          simpa using
            closedScalarRelativeEntropy_apply_of_pos (ξ₁ := 1) (ξ₂ := 1) (by norm_num)
              (by norm_num)
        rw [hone_value]
        exact EReal.coe_lt_top 0
      have hone_sum :
          ((1 : ℝ), (1 : ℝ)) ∈ effectiveDomain
            (((closedPerspective closed_relative_entropy_generator
              closed_relative_entropy_generator_mem_gammaZero.2.nonempty ∘
                ContinuousLinearEquiv.prodComm ℝ ℝ ℝ) +
              (fun p : ℝ × ℝ ↦ p.2 - p.1).toEReal)) := by
        simpa [closedScalarRelativeEntropy_eq_swapped_closedPerspective_add_affine] using hone_mem
      have hone_pair :
          ((1 : ℝ), (1 : ℝ)) ∈ effectiveDomain
              (closedPerspective closed_relative_entropy_generator
                closed_relative_entropy_generator_mem_gammaZero.2.nonempty ∘
                  ContinuousLinearEquiv.prodComm ℝ ℝ ℝ) ∧
            ((1 : ℝ), (1 : ℝ)) ∈ effectiveDomain ((fun p : ℝ × ℝ ↦ p.2 - p.1).toEReal) := by
        exact
          (mem_effectiveDomain_pointwiseAdd_iff
            (closedPerspective closed_relative_entropy_generator
              closed_relative_entropy_generator_mem_gammaZero.2.nonempty ∘
                ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)
            ((fun p : ℝ × ℝ ↦ p.2 - p.1).toEReal)
            (1, 1)).1 hone_sum
      exact ⟨(1, 1), hone_pair.1, hone_pair.2⟩
    -- Sum the two `Γ₀` owners along the concrete common-domain witness `(1, 1)`.
    exact pointwiseAdd_mem_gammaZero
      (closedPerspective closed_relative_entropy_generator
        closed_relative_entropy_generator_mem_gammaZero.2.nonempty ∘
          ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)
      ((fun p : ℝ × ℝ ↦ p.2 - p.1).toEReal)
      swapped_closedPerspective_mem_gammaZero
      affine_difference_toEReal_mem_gammaZero
      hdom
  simpa [closedScalarRelativeEntropy_eq_swapped_closedPerspective_add_affine] using hsum

/-- Helper for Example 11 25: every value of the source-facing scalar relative entropy is
nonnegative. -/
private theorem closedScalarRelativeEntropy_nonneg (p : ℝ × ℝ) :
    (0 : EReal) ≤ (closedScalarRelativeEntropy p : EReal) := by
  rcases p with ⟨ξ₁, ξ₂⟩
  by_cases hpos : 0 < ξ₁ ∧ 0 < ξ₂
  · -- On the positive orthant, rewrite the branch as `ξ₂ * klFun (ξ₁ / ξ₂)`.
    rw [closedScalarRelativeEntropy_apply, if_pos hpos]
    have hratio_nonneg : 0 ≤ ξ₁ / ξ₂ := div_nonneg hpos.1.le hpos.2.le
    have hkl_nonneg : 0 ≤ InformationTheory.klFun (ξ₁ / ξ₂) :=
      InformationTheory.klFun_nonneg hratio_nonneg
    have hreal_nonneg :
        0 ≤ ξ₁ * Real.log (ξ₁ / ξ₂) - ξ₁ + ξ₂ := by
      rw [closedScalarRelativeEntropy_pos_eq_mul_klFun hpos.1 hpos.2]
      exact mul_nonneg hpos.2.le hkl_nonneg
    exact_mod_cast hreal_nonneg
  · by_cases hzero : ξ₁ = 0 ∧ 0 ≤ ξ₂
    · -- Along `{0} × ℝ₊`, the value is the second coordinate.
      rw [closedScalarRelativeEntropy_apply, if_neg hpos, if_pos hzero]
      exact_mod_cast hzero.2
    · -- Everywhere else, the value is `+∞`.
      rw [closedScalarRelativeEntropy_apply, if_neg hpos, if_neg hzero]
      exact le_top

/- The infimum of `closedScalarRelativeEntropy` is `0`. -/
-- Proof sketch: evaluate the function at `(0, 0)` using the zero-left branch, and show every value
-- is bounded below by `0` through the nonnegativity of `InformationTheory.klFun`.
theorem closedScalarRelativeEntropy_sInf_eq_zero :
    sInf (Set.range f) = 0 := by
  have hzero_lb : ∀ y ∈ Set.range f, (0 : EReal) ≤ y := by
    intro y hy
    rcases hy with ⟨p, rfl⟩
    exact closedScalarRelativeEntropy_nonneg p
  have horigin : f (0, 0) = 0 := by
    -- The origin belongs to the zero-left branch with value `0`.
    simpa using closedScalarRelativeEntropy_apply_zero_left (ξ₂ := 0) (show 0 ≤ (0 : ℝ) by simp)
  have hsInf_le : sInf (Set.range f) ≤ 0 := by
    exact (isGLB_sInf (Set.range f)).1 ⟨(0, 0), horigin⟩
  have hzero_le : (0 : EReal) ≤ sInf (Set.range f) := by
    exact (isGLB_sInf (Set.range f)).2 hzero_lb
  exact le_antisymm hsInf_le hzero_le

/-- Helper for Example 11 25: the source-facing scalar relative entropy vanishes exactly on the
nonnegative diagonal. -/
private theorem closedScalarRelativeEntropy_eq_zero_iff {ξ₁ ξ₂ : ℝ} :
    (closedScalarRelativeEntropy (ξ₁, ξ₂) : EReal) = 0 ↔ 0 ≤ ξ₁ ∧ ξ₂ = ξ₁ := by
  by_cases hpos : 0 < ξ₁ ∧ 0 < ξ₂
  · -- On the positive orthant, rewrite through `klFun` and use its zero set `{1}`.
    rw [closedScalarRelativeEntropy_apply, if_pos hpos]
    constructor
    · intro hzero
      have hreal :
          ξ₁ * Real.log (ξ₁ / ξ₂) - ξ₁ + ξ₂ = 0 := by
        exact EReal.coe_eq_coe_iff.mp <| by simpa using hzero
      rw [closedScalarRelativeEntropy_pos_eq_mul_klFun hpos.1 hpos.2] at hreal
      have hratio :
          ξ₁ / ξ₂ = 1 := by
        refine (InformationTheory.klFun_eq_zero_iff (div_nonneg hpos.1.le hpos.2.le)).mp ?_
        rcases mul_eq_zero.mp hreal with hξ₂_zero | hkl_zero
        · exact (hpos.2.ne' hξ₂_zero).elim
        · exact hkl_zero
      exact ⟨hpos.1.le, ((div_eq_one_iff_eq hpos.2.ne').mp hratio).symm⟩
    · rintro ⟨_, hdiag⟩
      apply EReal.coe_eq_coe_iff.mpr
      rw [closedScalarRelativeEntropy_pos_eq_mul_klFun hpos.1 hpos.2, hdiag, div_self hpos.1.ne',
        InformationTheory.klFun_one]
      ring
  · by_cases hzero : ξ₁ = 0 ∧ 0 ≤ ξ₂
    · -- On the vertical branch, the value is `ξ₂`, so vanishing forces the origin.
      rcases hzero with ⟨hξ₁, hξ₂_nonneg⟩
      subst hξ₁
      rw [closedScalarRelativeEntropy_apply, if_neg hpos, if_pos ⟨rfl, hξ₂_nonneg⟩]
      constructor
      · intro hval
        have hξ₂_zero : ξ₂ = 0 := by
          exact EReal.coe_eq_coe_iff.mp <| by simpa using hval
        exact ⟨by simp, by simp [hξ₂_zero]⟩
      · rintro ⟨hξ₁_nonneg, hdiag⟩
        have hξ₂_zero : ξ₂ = 0 := by simpa using hdiag
        simp [hξ₂_zero]
    · -- Outside the first two branches, the value is `⊤`, so it cannot vanish.
      rw [closedScalarRelativeEntropy_apply, if_neg hpos, if_neg hzero]
      constructor
      · intro htop
        have : False := by
          simp at htop
        exact this.elim
      · intro hdiag
        rcases hdiag with ⟨hξ₁_nonneg, hdiag⟩
        by_cases hξ₁_zero : ξ₁ = 0
        · have hξ₂_nonneg : 0 ≤ ξ₂ := by
            rw [hdiag]
            exact hξ₁_nonneg
          exact (hzero ⟨hξ₁_zero, hξ₂_nonneg⟩).elim
        · have hξ₁_pos : 0 < ξ₁ := by
            exact lt_of_le_of_ne hξ₁_nonneg (by simpa [eq_comm] using hξ₁_zero)
          exact (hpos ⟨hξ₁_pos, by simpa [hdiag] using hξ₁_pos⟩).elim

/- The minimizers of `closedScalarRelativeEntropy` form the nonnegative diagonal ray. -/
-- Proof sketch: rewrite the positive-height branch as `ξ₂ * klFun (ξ₁ / ξ₂)` and use that
-- `InformationTheory.klFun` attains its minimum `0` exactly at `1`; the zero slice contributes
-- only the origin.
theorem closedScalarRelativeEntropy_argmin_eq :
    Argmin f =
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.2 = p.1} := by
  ext p
  rcases p with ⟨ξ₁, ξ₂⟩
  -- The infimum has already been computed to be `0`, so argmin membership is a zero-value test.
  rw [mem_argmin_iff_eq_sInf, closedScalarRelativeEntropy_sInf_eq_zero]
  exact closedScalarRelativeEntropy_eq_zero_iff

/-- The sequence `xₙ = (εₙ, εₙ)` from Example 11.25. -/
def example11_25xSequence (ε : ℕ → ℝ) : ℕ → ℝ × ℝ :=
  fun n ↦ (ε n, ε n)

/-- The sequence `yₙ = (εₙ, exp (-1 / εₙ))` from Example 11.25. -/
noncomputable def example11_25ySequence (ε : ℕ → ℝ) : ℕ → ℝ × ℝ :=
  fun n ↦ (ε n, Real.exp (-(1 / ε n)))

/-- The sequence `zₙ = (εₙ, exp (-1 / εₙ²))` from Example 11.25. -/
noncomputable def example11_25zSequence (ε : ℕ → ℝ) : ℕ → ℝ × ℝ :=
  fun n ↦ (ε n, Real.exp (-(1 / (ε n) ^ 2)))

/-- The diagonal sequence `xₙ` converges to the origin when `εₙ → 0`. -/
-- Proof sketch: both coordinates of `xₙ` are exactly `εₙ`, so product convergence follows from
-- the assumed scalar convergence.
theorem example11_25xSequence_tendsto_zero {ε : ℕ → ℝ}
    (hε_tendsto : Tendsto ε atTop (nhds 0)) :
    Tendsto (example11_25xSequence ε) atTop (nhds (0 : ℝ × ℝ)) := by
  -- Both coordinates are the same scalar sequence `εₙ`, so product convergence is immediate.
  simpa [example11_25xSequence] using
    Filter.Tendsto.prodMk_nhds hε_tendsto hε_tendsto

/-- Helper for Example 11 25: a positive real sequence converging to `0` has reciprocals tending
to `+∞`. -/
private theorem positive_sequence_inv_tendsto_atTop {ε : ℕ → ℝ}
    (hε_pos : ∀ n, 0 < ε n) (hε_tendsto : Tendsto ε atTop (nhds 0)) :
    Tendsto (fun n ↦ (ε n)⁻¹) atTop atTop := by
  -- Upgrade the limit to the right-sided neighborhood `0+`, then apply the inverse-limit lemma.
  have hε_right : Tendsto ε atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    change Tendsto ε atTop ((nhds (0 : ℝ)) ⊓ Filter.principal (Set.Ioi (0 : ℝ)))
    refine Filter.tendsto_inf.2 ⟨hε_tendsto, ?_⟩
    rw [Filter.tendsto_principal]
    exact Filter.Eventually.of_forall hε_pos
  simpa [one_div] using hε_right.inv_tendsto_nhdsGT_zero

/-- The exponentially perturbed sequence `yₙ` converges to the origin when `εₙ > 0` and
`εₙ → 0`. -/
-- Proof sketch: the first coordinate is `εₙ → 0`, while the second coordinate is
-- `exp (-(1 / εₙ))`, which tends to `0` because `1 / εₙ → +∞`.
theorem example11_25ySequence_tendsto_zero {ε : ℕ → ℝ} (hε_pos : ∀ n, 0 < ε n)
    (hε_tendsto : Tendsto ε atTop (nhds 0)) :
    Tendsto (example11_25ySequence ε) atTop (nhds (0 : ℝ × ℝ)) := by
  -- The first coordinate is `εₙ`, and the second is `exp (-(1 / εₙ))` with reciprocal exponent
  -- tending to `+∞`.
  have hinv : Tendsto (fun n ↦ (ε n)⁻¹) atTop atTop :=
    positive_sequence_inv_tendsto_atTop hε_pos hε_tendsto
  have hexp : Tendsto (fun n ↦ Real.exp (-((ε n)⁻¹))) atTop (nhds 0) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp hinv)
  have hpair :
      Tendsto (fun n ↦ (ε n, Real.exp (-((ε n)⁻¹)))) atTop (nhds (0 : ℝ × ℝ)) := by
    exact Filter.Tendsto.prodMk_nhds hε_tendsto hexp
  have hseq :
      example11_25ySequence ε = fun n ↦ (ε n, Real.exp (-((ε n)⁻¹))) := by
    funext n
    simp [example11_25ySequence, one_div]
  rw [hseq]
  exact hpair

/-- The faster-decaying sequence `zₙ` also converges to the origin when `εₙ > 0` and
`εₙ → 0`. -/
-- Proof sketch: the first coordinate is again `εₙ → 0`, and the second coordinate is
-- `exp (-(1 / εₙ²))`, which tends to `0` because `1 / εₙ² → +∞`.
theorem example11_25zSequence_tendsto_zero {ε : ℕ → ℝ} (hε_pos : ∀ n, 0 < ε n)
    (hε_tendsto : Tendsto ε atTop (nhds 0)) :
    Tendsto (example11_25zSequence ε) atTop (nhds (0 : ℝ × ℝ)) := by
  -- Apply the reciprocal-divergence lemma to the positive square sequence `εₙ²`.
  have hsq_pos : ∀ n, 0 < (ε n) ^ (2 : ℕ) := by
    intro n
    exact pow_pos (hε_pos n) 2
  have hsq_tendsto : Tendsto (fun n ↦ (ε n) ^ (2 : ℕ)) atTop (nhds 0) := by
    simpa [pow_two] using hε_tendsto.mul hε_tendsto
  have hinv_sq : Tendsto (fun n ↦ ((ε n) ^ (2 : ℕ))⁻¹) atTop atTop :=
    positive_sequence_inv_tendsto_atTop hsq_pos hsq_tendsto
  have hexp : Tendsto (fun n ↦ Real.exp (-(((ε n) ^ (2 : ℕ))⁻¹))) atTop (nhds 0) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp hinv_sq)
  have hpair :
      Tendsto (fun n ↦ (ε n, Real.exp (-(((ε n) ^ (2 : ℕ))⁻¹)))) atTop
        (nhds (0 : ℝ × ℝ)) := by
    exact Filter.Tendsto.prodMk_nhds hε_tendsto hexp
  have hseq :
      example11_25zSequence ε = fun n ↦ (ε n, Real.exp (-(((ε n) ^ (2 : ℕ))⁻¹))) := by
    funext n
    simp [example11_25zSequence, one_div]
  rw [hseq]
  exact hpair

/- Along the diagonal sequence `xₙ`, `closedScalarRelativeEntropy` is constantly `0`. -/
-- Proof sketch: if `εₙ > 0`, evaluate the positive branch at `ξ₁ = ξ₂ = εₙ`; if `εₙ = 0`, use
-- the zero-left branch. Nonnegativity is the exact hypothesis needed to stay on the diagonal
-- minimizer ray.
theorem closedScalarRelativeEntropy_value_xSequence {ε : ℕ → ℝ}
    (hε_nonneg : ∀ n, 0 ≤ ε n) (n : ℕ) :
    (closedScalarRelativeEntropy (example11_25xSequence ε n) : EReal) = 0 := by
  -- The diagonal lies exactly in the zero set characterized above.
  simpa [example11_25xSequence] using
    (closedScalarRelativeEntropy_eq_zero_iff (ξ₁ := ε n) (ξ₂ := ε n)).2 ⟨hε_nonneg n, rfl⟩

/- Along the diagonal sequence `xₙ`, the `closedScalarRelativeEntropy` values converge to `0`. -/
-- Proof sketch: the previous theorem shows that the sequence of values is constantly `0`.
theorem closedScalarRelativeEntropy_value_xSequence_tendsto_zero {ε : ℕ → ℝ}
    (hε_nonneg : ∀ n, 0 ≤ ε n) :
    Tendsto (fun n ↦ (closedScalarRelativeEntropy (example11_25xSequence ε n) : EReal))
      atTop (nhds (0 : EReal)) := by
  have hconst :
      (fun n ↦ (closedScalarRelativeEntropy (example11_25xSequence ε n) : EReal)) =
        fun _ : ℕ ↦ (0 : EReal) := by
    funext n
    exact closedScalarRelativeEntropy_value_xSequence hε_nonneg n
  rw [hconst]
  simp

/- Along the sequence `yₙ`, the `closedScalarRelativeEntropy` values converge to `1`. -/
-- Proof sketch: evaluate the positive branch at
-- `(εₙ, exp (-(1 / εₙ)))`, simplify the logarithm to obtain `1 - εₙ + exp (-(1 / εₙ))`, and
-- pass to the limit using `εₙ → 0`.
/-- Helper for Example 11 25: along `yₙ`, the positive branch of
`closedScalarRelativeEntropy` simplifies to the textbook real expression
`εₙ log εₙ + 1 - εₙ + exp (-(1 / εₙ))`. -/
private theorem closedScalarRelativeEntropy_value_ySequence_formula {ε : ℕ → ℝ}
    (hε_pos : ∀ n, 0 < ε n) (n : ℕ) :
    (closedScalarRelativeEntropy (example11_25ySequence ε n) : EReal) =
      ((ε n * Real.log (ε n) + 1 - ε n + Real.exp (-(1 / ε n)) : ℝ) : EReal) := by
  -- Evaluate on the positive branch, since both coordinates of `yₙ` are strictly positive.
  rw [example11_25ySequence,
    closedScalarRelativeEntropy_apply_of_pos (hε_pos n) (Real.exp_pos _)]
  have hlog :
      Real.log (ε n / Real.exp (-(1 / ε n))) = Real.log (ε n) + 1 / ε n := by
    rw [Real.log_div (hε_pos n).ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hmul : ε n * (1 / ε n) = 1 := by
    field_simp [(hε_pos n).ne']
  have hreal :
      ε n * Real.log (ε n / Real.exp (-(1 / ε n))) - ε n + Real.exp (-(1 / ε n)) =
        ε n * Real.log (ε n) + 1 - ε n + Real.exp (-(1 / ε n)) := by
    rw [hlog]
    calc
      ε n * (Real.log (ε n) + 1 / ε n) - ε n + Real.exp (-(1 / ε n)) =
          ε n * Real.log (ε n) + ε n * (1 / ε n) - ε n + Real.exp (-(1 / ε n)) := by
            ring
      _ = ε n * Real.log (ε n) + 1 - ε n + Real.exp (-(1 / ε n)) := by
            rw [hmul]
  exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal

theorem closedScalarRelativeEntropy_value_ySequence_tendsto_one {ε : ℕ → ℝ}
    (hε_pos : ∀ n, 0 < ε n)
    (hε_tendsto : Tendsto ε atTop (nhds 0)) :
    Tendsto (fun n ↦ (closedScalarRelativeEntropy (example11_25ySequence ε n) : EReal))
      atTop (nhds (1 : EReal)) := by
  have hvalues :
      (fun n ↦ (closedScalarRelativeEntropy (example11_25ySequence ε n) : EReal)) =
        fun n ↦ ((ε n * Real.log (ε n) + 1 - ε n + Real.exp (-(1 / ε n)) : ℝ) : EReal) := by
    funext n
    exact closedScalarRelativeEntropy_value_ySequence_formula hε_pos n
  -- Upgrade `εₙ → 0` to the right-sided neighborhood so the standard `x log x → 0` lemma applies.
  have hε_right : Tendsto ε atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    change Tendsto ε atTop ((nhds (0 : ℝ)) ⊓ Filter.principal (Set.Ioi (0 : ℝ)))
    refine Filter.tendsto_inf.2 ⟨hε_tendsto, ?_⟩
    rw [Filter.tendsto_principal]
    exact Filter.Eventually.of_forall hε_pos
  have hlog_mul : Tendsto (fun n ↦ ε n * Real.log (ε n)) atTop (nhds (0 : ℝ)) := by
    simpa [Real.rpow_one, mul_comm] using
      (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one).comp hε_right
  have hinv : Tendsto (fun n ↦ (ε n)⁻¹) atTop atTop :=
    positive_sequence_inv_tendsto_atTop hε_pos hε_tendsto
  have hexp : Tendsto (fun n ↦ Real.exp (-((ε n)⁻¹))) atTop (nhds (0 : ℝ)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp hinv)
  have hreal :
      Tendsto
        (fun n ↦ ε n * Real.log (ε n) + (1 - ε n) + Real.exp (-((ε n)⁻¹)))
        atTop (nhds (1 : ℝ)) := by
    simpa using (hlog_mul.add (tendsto_const_nhds.sub hε_tendsto)).add hexp
  rw [hvalues]
  -- Transport the real-valued limit through the canonical coercion into `EReal`.
  simpa [one_div, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (EReal.tendsto_coe.2 hreal)

/- Along the sequence `zₙ`, the `closedScalarRelativeEntropy` values diverge to `+∞`. -/
-- Proof sketch: evaluate the positive branch at
-- `(εₙ, exp (-(1 / εₙ²)))`, simplify to `1 / εₙ - εₙ + exp (-(1 / εₙ²))`, and use
-- `εₙ → 0` to force `1 / εₙ → +∞`.
/-- Helper for Example 11 25: along `zₙ`, the positive branch of
`closedScalarRelativeEntropy` simplifies to the textbook real expression
`εₙ log εₙ + 1 / εₙ - εₙ + exp (-(1 / εₙ²))`. -/
private theorem closedScalarRelativeEntropy_value_zSequence_formula {ε : ℕ → ℝ}
    (hε_pos : ∀ n, 0 < ε n) (n : ℕ) :
    (closedScalarRelativeEntropy (example11_25zSequence ε n) : EReal) =
      ((ε n * Real.log (ε n) + 1 / ε n - ε n + Real.exp (-(1 / (ε n) ^ 2)) : ℝ) : EReal) := by
  -- Evaluate on the positive branch, since both coordinates of `zₙ` are strictly positive.
  rw [example11_25zSequence,
    closedScalarRelativeEntropy_apply_of_pos (hε_pos n) (Real.exp_pos _)]
  have hlog :
      Real.log (ε n / Real.exp (-(1 / (ε n) ^ 2))) = Real.log (ε n) + 1 / (ε n) ^ 2 := by
    rw [Real.log_div (hε_pos n).ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hmul : ε n * (1 / (ε n) ^ 2) = 1 / ε n := by
    field_simp [pow_two, (hε_pos n).ne']
  have hreal :
      ε n * Real.log (ε n / Real.exp (-(1 / (ε n) ^ 2))) - ε n +
          Real.exp (-(1 / (ε n) ^ 2)) =
        ε n * Real.log (ε n) + 1 / ε n - ε n + Real.exp (-(1 / (ε n) ^ 2)) := by
    rw [hlog]
    calc
      ε n * (Real.log (ε n) + 1 / (ε n) ^ 2) - ε n + Real.exp (-(1 / (ε n) ^ 2)) =
          ε n * Real.log (ε n) + ε n * (1 / (ε n) ^ 2) - ε n +
            Real.exp (-(1 / (ε n) ^ 2)) := by
              ring
      _ = ε n * Real.log (ε n) + 1 / ε n - ε n + Real.exp (-(1 / (ε n) ^ 2)) := by
            rw [hmul]
  exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal

/-- Helper for Example 11 25: the `zₙ` values dominate the divergent lower bound
`1 / εₙ - 1`. -/
private theorem closedScalarRelativeEntropy_value_zSequence_ge_inv_sub_one {ε : ℕ → ℝ}
    (hε_pos : ∀ n, 0 < ε n) (n : ℕ) :
    (((1 / ε n - 1 : ℝ) : EReal)) ≤
      (closedScalarRelativeEntropy (example11_25zSequence ε n) : EReal) := by
  rw [closedScalarRelativeEntropy_value_zSequence_formula hε_pos n]
  -- The entropy defect inequality gives the lower bound `εₙ - 1 ≤ εₙ log εₙ`.
  have hlog_mul :
      ε n - 1 ≤ ε n * Real.log (ε n) := by
    have hmul :=
      mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos (hε_pos n)) (hε_pos n).le
    have hleft : ε n * (1 - (ε n)⁻¹) = ε n - 1 := by
      field_simp [(hε_pos n).ne']
    rw [hleft] at hmul
    exact hmul
  have hexp_nonneg : 0 ≤ Real.exp (-(1 / (ε n) ^ 2)) := (Real.exp_pos _).le
  have hbound :
      1 / ε n - 1 ≤ ε n * Real.log (ε n) + 1 / ε n - ε n + Real.exp (-(1 / (ε n) ^ 2)) := by
    linarith
  exact_mod_cast hbound

theorem closedScalarRelativeEntropy_value_zSequence_tendsto_top {ε : ℕ → ℝ}
    (hε_pos : ∀ n, 0 < ε n)
    (hε_tendsto : Tendsto ε atTop (nhds 0)) :
    Tendsto (fun n ↦ (closedScalarRelativeEntropy (example11_25zSequence ε n) : EReal))
      atTop (nhds (⊤ : EReal)) := by
  have hinv : Tendsto (fun n ↦ (ε n)⁻¹) atTop atTop :=
    positive_sequence_inv_tendsto_atTop hε_pos hε_tendsto
  rw [EReal.tendsto_nhds_top_iff_real]
  intro M
  have hlarge : ∀ᶠ n in atTop, M + 2 ≤ (ε n)⁻¹ :=
    Filter.tendsto_atTop.mp hinv (M + 2)
  filter_upwards [hlarge] with n hn
  have hrecip : M + 2 ≤ 1 / ε n := by
    simpa [one_div] using hn
  have hlt_real : M < 1 / ε n - 1 := by
    linarith
  -- Compare with the explicit divergent lower bound `1 / εₙ - 1`.
  exact lt_of_lt_of_le (by exact_mod_cast hlt_real)
    (closedScalarRelativeEntropy_value_zSequence_ge_inv_sub_one hε_pos n)

/- The origin lies in the minimizer set of `closedScalarRelativeEntropy`. -/
-- Proof sketch: rewrite `Argmin` using `closedScalarRelativeEntropy_argmin_eq` and evaluate the
-- defining set
-- predicate at `(0, 0)`.
theorem closedScalarRelativeEntropy_origin_mem_argmin :
    (0 : ℝ × ℝ) ∈ Argmin f := by
  -- Replace `Argmin f` by the diagonal ray description and evaluate at the origin.
  rw [closedScalarRelativeEntropy_argmin_eq]
  simp

/-- Example 11 25: for every positive sequence `εₙ → 0`, the sequences
`xₙ = (εₙ, εₙ)`, `yₙ = (εₙ, exp (-1 / εₙ))`, and `zₙ = (εₙ, exp (-1 / εₙ²))`
all converge to the minimizer `(0, 0)`, while the corresponding function values converge to
`0`, `1`, and `+∞`, respectively. -/
-- Proof sketch: use `closedScalarRelativeEntropy_origin_mem_argmin` for the minimizer claim,
-- combine the three
-- sequence convergence theorems with the three separate value-limit theorems.
theorem example11_25_same_limit_different_value_limits {ε : ℕ → ℝ} (hε_pos : ∀ n, 0 < ε n)
    (hε_tendsto : Tendsto ε atTop (nhds 0)) :
    (0 : ℝ × ℝ) ∈ Argmin f ∧
      Tendsto (example11_25xSequence ε) atTop (nhds (0 : ℝ × ℝ)) ∧
      Tendsto (example11_25ySequence ε) atTop (nhds (0 : ℝ × ℝ)) ∧
      Tendsto (example11_25zSequence ε) atTop (nhds (0 : ℝ × ℝ)) ∧
      Tendsto (fun n ↦ (closedScalarRelativeEntropy (example11_25xSequence ε n) : EReal))
        atTop (nhds (0 : EReal)) ∧
      Tendsto (fun n ↦ (closedScalarRelativeEntropy (example11_25ySequence ε n) : EReal))
        atTop (nhds (1 : EReal)) ∧
      Tendsto (fun n ↦ (closedScalarRelativeEntropy (example11_25zSequence ε n) : EReal))
        atTop (nhds (⊤ : EReal)) := by
  refine ⟨closedScalarRelativeEntropy_origin_mem_argmin,
    example11_25xSequence_tendsto_zero hε_tendsto,
    example11_25ySequence_tendsto_zero hε_pos hε_tendsto,
    example11_25zSequence_tendsto_zero hε_pos hε_tendsto,
    closedScalarRelativeEntropy_value_xSequence_tendsto_zero (fun n ↦ (hε_pos n).le),
    closedScalarRelativeEntropy_value_ySequence_tendsto_one hε_pos hε_tendsto,
    closedScalarRelativeEntropy_value_zSequence_tendsto_top hε_pos hε_tendsto⟩

end ERealFunction
