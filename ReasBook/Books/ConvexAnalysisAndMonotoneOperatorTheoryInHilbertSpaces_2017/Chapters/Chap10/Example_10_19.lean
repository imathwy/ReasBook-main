import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap10.Definition_10_7
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

/-- The explicit `EReal`-valued formula from Example 10.19 on `ℝ²`. -/
noncomputable def example10_19FunctionEReal : (ℝ × ℝ) → EReal :=
  fun x ↦
    if x.1 = 0 ∧ x.2 = 0 then
      0
    else if 0 < x.1 ∧ 0 < x.2 then
      (((x.2 ^ (2 : ℕ)) / (2 * x.1) + x.2 ^ (2 : ℕ) : ℝ) : EReal)
    else
      ⊤

-- Proof sketch: split on the three defining branches of `example10_19FunctionEReal`. The origin
-- branch gives `0`, the positive-orthant branch is a real number, and the remaining branch gives
-- `⊤`; all three values lie strictly above `⊥`.
/-- The explicit formula from Example 10.19 never takes the value `-∞`. -/
theorem example10_19FunctionEReal_gt_bot (x : ℝ × ℝ) :
    ⊥ < example10_19FunctionEReal x := by
  -- Split into the three defining branches of the `EReal` formula.
  by_cases h0 : x.1 = 0 ∧ x.2 = 0
  · simp [example10_19FunctionEReal, h0]
  · by_cases hpos : 0 < x.1 ∧ 0 < x.2
    · simpa [example10_19FunctionEReal, h0, hpos] using
        (EReal.bot_lt_coe (((x.2 ^ (2 : ℕ)) / (2 * x.1) + x.2 ^ (2 : ℕ) : ℝ)))
    · simp [example10_19FunctionEReal, h0, hpos]

/-- The `]-∞,+∞]`-valued function from Example 10.19. -/
noncomputable def example10_19Function : (ℝ × ℝ) → Set.Ioi (⊥ : EReal) :=
  fun x ↦ ⟨example10_19FunctionEReal x, example10_19FunctionEReal_gt_bot x⟩

/-- Coercing the Example 10.19 function to `EReal` recovers its explicit formula. -/
@[simp] theorem example10_19Function_apply (x : ℝ × ℝ) :
    example10_19Function.asEReal x = example10_19FunctionEReal x :=
  rfl

-- Proof sketch: outside the origin, the only finite branch of the explicit formula is the open
-- positive orthant branch; every other point maps to `⊤`.
/-- The effective domain in Example 10.19 is the origin together with the open positive orthant. -/
theorem mem_effectiveDomain_example10_19Function_iff (x : ℝ × ℝ) :
    x ∈ effectiveDomain example10_19Function ↔ x = (0, 0) ∨ 0 < x.1 ∧ 0 < x.2 := by
  rcases x with ⟨ξ, η⟩
  -- Split into the origin, positive-orthant, and `⊤` branches of the explicit formula.
  rw [mem_effectiveDomain_iff]
  by_cases h0 : ξ = 0 ∧ η = 0
  · rcases h0 with ⟨rfl, rfl⟩
    simp [example10_19Function_apply, example10_19FunctionEReal]
  · by_cases hpos : 0 < ξ ∧ 0 < η
    · have hfinite :
          (((η ^ (2 : ℕ)) / (2 * ξ) : ℝ) : EReal) + ((η ^ (2 : ℕ) : ℝ) : EReal) < ⊤ :=
        EReal.add_lt_top (EReal.coe_ne_top _) (EReal.coe_ne_top _)
      simpa [example10_19Function_apply, example10_19FunctionEReal, h0, hpos] using hfinite
    · simp [example10_19Function_apply, example10_19FunctionEReal, h0, hpos]

/-- The set `C = B(0; ρ) ∩ dom f` from Example 10.19. -/
def example10_19Set (ρ : Set.Ioi (0 : ℝ)) : Set (ℝ × ℝ) :=
  Metric.ball (0 : ℝ × ℝ) (ρ : ℝ) ∩ effectiveDomain example10_19Function

/-- Membership in `C = B(0; ρ) ∩ dom f` is membership in the ball together with the explicit
domain condition from Example 10.19. -/
@[simp] theorem mem_example10_19Set_iff (ρ : Set.Ioi (0 : ℝ)) (x : ℝ × ℝ) :
    x ∈ example10_19Set ρ ↔
      x ∈ Metric.ball (0 : ℝ × ℝ) (ρ : ℝ) ∧
        (x = (0, 0) ∨ 0 < x.1 ∧ 0 < x.2) := by
  rw [example10_19Set, Set.mem_inter_iff, mem_effectiveDomain_example10_19Function_iff]

/-- Helper for Example 10.19: the finite positive-orthant branch as a real-valued formula. -/
private noncomputable def positiveBranchFormula (x : ℝ × ℝ) : ℝ :=
  x.2 ^ (2 : ℕ) / (2 * x.1) + x.2 ^ (2 : ℕ)

/-- Helper for Example 10.19: on the positive orthant, the `EReal` function equals the explicit
finite real branch. -/
private theorem positiveBranchFormula_eq (x : ℝ × ℝ) (hx : 0 < x.1 ∧ 0 < x.2) :
    example10_19Function.asEReal x = ((positiveBranchFormula x : ℝ) : EReal) := by
  -- Rewrite the defining `if` once and stay in the positive-branch normal form.
  simp [example10_19Function_apply, example10_19FunctionEReal, hx, hx.1.ne', hx.2.ne',
    positiveBranchFormula]

/-- Helper for Example 10.19: scaling a positive-branch point toward the origin gives the exact
ray Jensen gap used in the source proof. -/
private theorem positiveBranchRayGapEq {β ξ η : ℝ}
    (hβ : 0 < β) (hξ : 0 < ξ) :
    β * positiveBranchFormula (ξ, η) - positiveBranchFormula (β • ((ξ, η) : ℝ × ℝ)) =
      β * (1 - β) * η ^ (2 : ℕ) := by
  -- Expand the scaled branch once; the quadratic-over-linear term collapses to a linear factor.
  dsimp [positiveBranchFormula]
  field_simp [hβ.ne', hξ.ne']
  ring

/-- Helper for Example 10.19: moving a positive-branch point strictly toward the origin decreases
the positive branch by the exact ray gap. -/
private theorem positiveBranchRayStrict {β ξ η : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hξ : 0 < ξ) (hη : 0 < η) :
    positiveBranchFormula (β • ((ξ, η) : ℝ × ℝ)) < β * positiveBranchFormula (ξ, η) := by
  have hβgap : 0 < β * (1 - β) * η ^ (2 : ℕ) := by
    have hβ' : 0 < 1 - β := by linarith
    positivity
  have hgap := positiveBranchRayGapEq (β := β) (ξ := ξ) (η := η) hβ0 hξ
  nlinarith

/-- Helper for Example 10.19: the function is nonnegative on its effective domain. -/
private theorem example10_19Function_nonneg_of_mem_effectiveDomain (x : ℝ × ℝ)
    (hx : x ∈ effectiveDomain example10_19Function) :
    (0 : EReal) ≤ example10_19Function.asEReal x := by
  rcases (mem_effectiveDomain_example10_19Function_iff x).1 hx with rfl | hxpos
  · -- The origin branch is exactly `0`.
    simp [example10_19Function_apply, example10_19FunctionEReal]
  · -- On the positive orthant, the explicit real formula is manifestly nonnegative.
    rw [positiveBranchFormula_eq x hxpos]
    have hnonneg : 0 ≤ positiveBranchFormula x := by
      dsimp [positiveBranchFormula]
      have hdiv : 0 ≤ x.2 ^ (2 : ℕ) / (2 * x.1) := by
        refine div_nonneg ?_ ?_
        · positivity
        · nlinarith [hxpos.1]
      have hsq : 0 ≤ x.2 ^ (2 : ℕ) := by
        positivity
      linarith
    exact_mod_cast hnonneg

/-- Helper for Example 10.19: the effective domain is convex. -/
private theorem effectiveDomain_example10_19Function_convex :
    Convex ℝ (effectiveDomain example10_19Function) := by
  refine (convex_iff_forall_pos).2 ?_
  intro x hx y hy a b ha hb hab
  rcases (mem_effectiveDomain_example10_19Function_iff x).1 hx with rfl | hxpos
  · rcases (mem_effectiveDomain_example10_19Function_iff y).1 hy with rfl | hypos
    · -- The convex combination of the origin with itself is the origin.
      simpa using
        (mem_effectiveDomain_example10_19Function_iff ((0, 0) : ℝ × ℝ)).2 (Or.inl rfl)
    · -- Positive weights keep the combination with a positive-orthant point in the
      -- positive orthant.
      refine (mem_effectiveDomain_example10_19Function_iff (a • ((0, 0) : ℝ × ℝ) + b • y)).2 ?_
      right
      constructor
      · change 0 < a * 0 + b * y.1
        nlinarith [hb, hypos.1]
      · change 0 < a * 0 + b * y.2
        nlinarith [hb, hypos.2]
  · rcases (mem_effectiveDomain_example10_19Function_iff y).1 hy with rfl | hypos
    · -- The symmetric origin/positive-orthant case is the same computation.
      refine (mem_effectiveDomain_example10_19Function_iff (a • x + b • ((0, 0) : ℝ × ℝ))).2 ?_
      right
      constructor
      · change 0 < a * x.1 + b * 0
        nlinarith [ha, hxpos.1]
      · change 0 < a * x.2 + b * 0
        nlinarith [ha, hxpos.2]
    · -- Positive coordinates stay positive under a strictly positive convex combination.
      refine (mem_effectiveDomain_example10_19Function_iff (a • x + b • y)).2 ?_
      right
      constructor
      · change 0 < a * x.1 + b * y.1
        nlinarith [ha, hb, hxpos.1, hypos.1]
      · change 0 < a * x.2 + b * y.2
        nlinarith [ha, hb, hxpos.2, hypos.2]

/-- Helper for Example 10.19: the quadratic-over-linear term satisfies the two-point Jensen
inequality on the positive orthant. -/
private theorem quadraticOverLinear_jensen_le
    {a b ξ₁ ξ₂ η₁ η₂ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hξ₁ : 0 < ξ₁) (hξ₂ : 0 < ξ₂) :
    ((a * η₁ + b * η₂) ^ (2 : ℕ)) / (2 * (a * ξ₁ + b * ξ₂)) ≤
      a * (η₁ ^ (2 : ℕ) / (2 * ξ₁)) + b * (η₂ ^ (2 : ℕ) / (2 * ξ₂)) := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · rcases eq_or_lt_of_le hb with rfl | hb_pos
    · -- When both weights vanish, every term is zero by definition of division in a field.
      simp
    · -- With `a = 0`, the inequality is an equality after cancelling the positive `b ξ₂`.
      have hEq :
          ((0 * η₁ + b * η₂) ^ (2 : ℕ)) / (2 * (0 * ξ₁ + b * ξ₂)) =
            0 * (η₁ ^ (2 : ℕ) / (2 * ξ₁)) + b * (η₂ ^ (2 : ℕ) / (2 * ξ₂)) := by
        field_simp [hb_pos.ne', hξ₂.ne']
        ring
      linarith
  · rcases eq_or_lt_of_le hb with rfl | hb_pos
    · -- The symmetric `b = 0` case is the same cancellation argument.
      have hEq :
          ((a * η₁ + 0 * η₂) ^ (2 : ℕ)) / (2 * (a * ξ₁ + 0 * ξ₂)) =
            a * (η₁ ^ (2 : ℕ) / (2 * ξ₁)) + 0 * (η₂ ^ (2 : ℕ) / (2 * ξ₂)) := by
        field_simp [ha_pos.ne', hξ₁.ne']
        ring
      linarith
    · -- Route correction: use the square-remainder factorization instead of repeated in-place
      -- denominator clearing.
      have hsum_pos : 0 < a * ξ₁ + b * ξ₂ := by
        positivity
      have hgap :
          a * (η₁ ^ (2 : ℕ) / (2 * ξ₁)) + b * (η₂ ^ (2 : ℕ) / (2 * ξ₂)) -
              ((a * η₁ + b * η₂) ^ (2 : ℕ)) / (2 * (a * ξ₁ + b * ξ₂)) =
            (a * b * (η₁ * ξ₂ - η₂ * ξ₁) ^ (2 : ℕ)) /
              (2 * ξ₁ * ξ₂ * (a * ξ₁ + b * ξ₂)) := by
        field_simp [hξ₁.ne', hξ₂.ne', hsum_pos.ne']
        ring
      have hgap_nonneg :
          0 ≤
            (a * b * (η₁ * ξ₂ - η₂ * ξ₁) ^ (2 : ℕ)) /
              (2 * ξ₁ * ξ₂ * (a * ξ₁ + b * ξ₂)) := by
        refine div_nonneg ?_ ?_
        · positivity
        · positivity
      nlinarith

/-- Helper for Example 10.19: with equal second coordinates, the quadratic-over-linear term is
strictly Jensen convex as soon as the first coordinates differ. -/
private theorem quadraticOverLinear_sameSecond_strict
    {a b ξ₁ ξ₂ η : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hξ₁ : 0 < ξ₁) (hξ₂ : 0 < ξ₂) (hη : 0 < η) (hξ : ξ₁ ≠ ξ₂) :
    ((a * η + b * η) ^ (2 : ℕ)) / (2 * (a * ξ₁ + b * ξ₂)) <
      a * (η ^ (2 : ℕ) / (2 * ξ₁)) + b * (η ^ (2 : ℕ) / (2 * ξ₂)) := by
  -- Route correction: factor the gap as a positive square remainder instead of reopening the
  -- denominator normalization inside the strict Jensen proof.
  have hsum_pos : 0 < a * ξ₁ + b * ξ₂ := by
    positivity
  have hgap :
      a * (η ^ (2 : ℕ) / (2 * ξ₁)) + b * (η ^ (2 : ℕ) / (2 * ξ₂)) -
          ((a * η + b * η) ^ (2 : ℕ)) / (2 * (a * ξ₁ + b * ξ₂)) =
        (a * b * η ^ (2 : ℕ) * (ξ₁ - ξ₂) ^ (2 : ℕ)) /
          (2 * ξ₁ * ξ₂ * (a * ξ₁ + b * ξ₂)) := by
    field_simp [hξ₁.ne', hξ₂.ne', hsum_pos.ne']
    ring
  have hnum_pos : 0 < a * b * η ^ (2 : ℕ) * (ξ₁ - ξ₂) ^ (2 : ℕ) := by
    refine mul_pos ?_ (sq_pos_of_ne_zero (sub_ne_zero.mpr hξ))
    refine mul_pos (mul_pos ha hb) ?_
    positivity
  have hgap_pos :
      0 <
        (a * b * η ^ (2 : ℕ) * (ξ₁ - ξ₂) ^ (2 : ℕ)) /
          (2 * ξ₁ * ξ₂ * (a * ξ₁ + b * ξ₂)) := by
    exact div_pos hnum_pos (by positivity)
  nlinarith

/-- Helper for Example 10.19: the strict Jensen inequality on the positive orthant. -/
private theorem strictJensen_positiveOrthant
    {x y : ℝ × ℝ} (hx : 0 < x.1 ∧ 0 < x.2) (hy : 0 < y.1 ∧ 0 < y.2) (hxy : x ≠ y)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    example10_19Function.asEReal (α • x + (1 - α) • y) <
      (α : EReal) * example10_19Function.asEReal x +
        (1 - α : EReal) * example10_19Function.asEReal y := by
  rcases x with ⟨ξ₁, η₁⟩
  rcases y with ⟨ξ₂, η₂⟩
  have hβ : 0 < 1 - α := by
    linarith
  have hmid_pos :
      0 < α * ξ₁ + (1 - α) * ξ₂ ∧ 0 < α * η₁ + (1 - α) * η₂ := by
    constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2, hα0, hβ]
  -- Rewrite all three values through the finite positive branch and then work in `ℝ`.
  rw [positiveBranchFormula_eq (α • (ξ₁, η₁) + (1 - α) • (ξ₂, η₂)) hmid_pos,
    positiveBranchFormula_eq (ξ₁, η₁) hx, positiveBranchFormula_eq (ξ₂, η₂) hy,
    ← EReal.coe_mul]
  have hβ_cast : (1 - α : EReal) = (((1 - α : ℝ)) : EReal) := by
    exact_mod_cast rfl
  rw [hβ_cast, ← EReal.coe_mul, ← EReal.coe_add]
  apply EReal.coe_lt_coe_iff.mpr
  by_cases hηeq : η₁ = η₂
  · have hξneq : ξ₁ ≠ ξ₂ := by
      intro hξeq
      apply hxy
      ext <;> assumption
    have hquad :
        ((α * η₁ + (1 - α) * η₁) ^ (2 : ℕ)) / (2 * (α * ξ₁ + (1 - α) * ξ₂)) <
          α * (η₁ ^ (2 : ℕ) / (2 * ξ₁)) + (1 - α) * (η₁ ^ (2 : ℕ) / (2 * ξ₂)) :=
      quadraticOverLinear_sameSecond_strict hα0 hβ hx.1 hy.1 hx.2 hξneq
    -- With equal second coordinates, the square terms cancel and strictness comes entirely from
    -- the reciprocal branch.
    have hleft :
        positiveBranchFormula (α • (ξ₁, η₁) + (1 - α) • (ξ₂, η₂)) =
          ((α * η₁ + (1 - α) * η₁) ^ (2 : ℕ)) / (2 * (α * ξ₁ + (1 - α) * ξ₂)) +
            η₁ ^ (2 : ℕ) := by
      simp [positiveBranchFormula, hηeq]
      ring
    have hright :
        α * positiveBranchFormula (ξ₁, η₁) + (1 - α) * positiveBranchFormula (ξ₂, η₂) =
          α * (η₁ ^ (2 : ℕ) / (2 * ξ₁)) + (1 - α) * (η₁ ^ (2 : ℕ) / (2 * ξ₂)) +
            η₁ ^ (2 : ℕ) := by
      simp [positiveBranchFormula, hηeq]
      ring
    rw [hleft, hright]
    linarith
  · have hsquare :
      (α * η₁ + (1 - α) * η₂) ^ (2 : ℕ) <
        α * η₁ ^ (2 : ℕ) + (1 - α) * η₂ ^ (2 : ℕ) := by
      have hsq_gap :
          α * η₁ ^ (2 : ℕ) + (1 - α) * η₂ ^ (2 : ℕ) -
              (α * η₁ + (1 - α) * η₂) ^ (2 : ℕ) =
            α * (1 - α) * (η₁ - η₂) ^ (2 : ℕ) := by
        ring
      have hsq_gap_pos : 0 < α * (1 - α) * (η₁ - η₂) ^ (2 : ℕ) := by
        refine mul_pos (mul_pos hα0 hβ) (sq_pos_of_ne_zero (sub_ne_zero.mpr hηeq))
      nlinarith [hsq_gap, hsq_gap_pos]
    have hquad :
        ((α * η₁ + (1 - α) * η₂) ^ (2 : ℕ)) / (2 * (α * ξ₁ + (1 - α) * ξ₂)) ≤
          α * (η₁ ^ (2 : ℕ) / (2 * ξ₁)) + (1 - α) * (η₂ ^ (2 : ℕ) / (2 * ξ₂)) :=
      quadraticOverLinear_jensen_le hα0.le hβ.le hx.1 hy.1
    -- When the second coordinates differ, the added square term yields the strict gap.
    dsimp [positiveBranchFormula]
    nlinarith [hquad, hsquare]

/-- Helper for Example 10.19: an interior point `(r, η)` with `0 < η < r < ρ` lies in `C`. -/
private theorem innerPoint_mem_set (ρ : Set.Ioi (0 : ℝ)) {r η : ℝ}
    (hr : 0 < r) (hrρ : r < (ρ : ℝ)) (hη0 : 0 < η) (hηr : η < r) :
    (r, η) ∈ example10_19Set ρ := by
  refine ⟨?_, ?_⟩
  · -- In the product max norm, `‖(r, η)‖ = max r η`, so the ball condition is immediate.
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [sub_zero]
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr, abs_of_pos hη0,
      max_lt_iff]
    exact ⟨hrρ, lt_trans hηr hrρ⟩
  · -- The witness lies in the positive orthant branch of the effective domain.
    exact (mem_effectiveDomain_example10_19Function_iff (r, η)).2 <| Or.inr ⟨hr, hη0⟩

/-- Helper for Example 10.19: for `0 < η < r`, the point `(r, η)` has `NNReal` norm `r`. -/
private theorem innerPoint_nnnorm_eq {r η : ℝ} (hr : 0 < r) (hη0 : 0 < η) (hηr : η < r) :
    ‖((r, η) : ℝ × ℝ) - (0, 0)‖₊ = ⟨r, hr.le⟩ := by
  apply Subtype.ext
  -- Rewrite the product norm as a max norm and use `η < r`.
  simp [Real.norm_eq_abs, abs_of_pos hr, abs_of_pos hη0, max_eq_left hηr.le]

/-- Helper for Example 10.19: at the midpoint of `(r, η)` and `0`, the Jensen gap equals
`η² / 4`. -/
private theorem innerPoint_gap_eq {r η : ℝ} (hr : 0 < r) (hη0 : 0 < η) :
    jensenGap example10_19Function (1 / 2) (r, η) (0, 0) =
      (((η ^ (2 : ℕ)) / 4 : ℝ) : EReal) := by
  let m : ℝ × ℝ := (1 / 2 : ℝ) • ((r, η) : ℝ × ℝ) + (1 - 1 / 2) • (0, 0)
  have hhalf_pos : 0 < (1 / 2 : ℝ) := by norm_num
  have hreal_scaled :
      (1 / 2 : ℝ) * positiveBranchFormula (r, η) -
          positiveBranchFormula ((1 / 2 : ℝ) • ((r, η) : ℝ × ℝ)) =
        (η ^ (2 : ℕ)) / 4 := by
    -- The midpoint gap is the ray-gap identity specialized to the midpoint coefficient.
    calc
      (1 / 2 : ℝ) * positiveBranchFormula (r, η) -
          positiveBranchFormula ((1 / 2 : ℝ) • ((r, η) : ℝ × ℝ)) =
          (1 / 2 : ℝ) * (1 - 1 / 2) * η ^ (2 : ℕ) := by
            simpa using
              positiveBranchRayGapEq (β := (1 / 2 : ℝ)) (ξ := r) (η := η) hhalf_pos hr
      _ = (η ^ (2 : ℕ)) / 4 := by ring
  have hreal :
      (1 / 2 : ℝ) * positiveBranchFormula (r, η) - positiveBranchFormula m =
        (η ^ (2 : ℕ)) / 4 := by
    simpa [m, Prod.smul_mk] using hreal_scaled
  -- Rewrite the endpoint and midpoint through the finite branch and recast the real identity.
  have hx_eq :
      ((example10_19Function (r, η) : Set.Ioi (⊥ : EReal)) : EReal) =
        ((positiveBranchFormula (r, η) : ℝ) : EReal) := by
    simpa [Function.asEReal_apply] using positiveBranchFormula_eq (r, η) ⟨hr, hη0⟩
  have hzero :
      ((example10_19Function (0, 0) : Set.Ioi (⊥ : EReal)) : EReal) = 0 := by
    simp [example10_19Function_apply, example10_19FunctionEReal]
  have hmid_eq :
      example10_19FunctionEReal (((2 : ℝ)⁻¹ * r), ((2 : ℝ)⁻¹ * η)) =
        ((positiveBranchFormula (((2 : ℝ)⁻¹ * r), ((2 : ℝ)⁻¹ * η)) : ℝ) : EReal) := by
    have hmid_pos :
        0 < ((2 : ℝ)⁻¹ * r) ∧ 0 < ((2 : ℝ)⁻¹ * η) := by
      constructor <;> nlinarith
    simpa [example10_19Function_apply] using
      positiveBranchFormula_eq (((2 : ℝ)⁻¹ * r), ((2 : ℝ)⁻¹ * η)) hmid_pos
  rw [jensenGap, hx_eq, hzero]
  simpa [m, hmid_eq, Prod.smul_mk, sub_eq_add_neg, ← EReal.coe_sub, EReal.coe_mul] using
    congrArg (fun t : ℝ ↦ (t : EReal)) hreal

/-- Helper for Example 10.19: a sufficiently small ball around a positive point stays in the
open positive orthant. -/
private theorem positiveOrthant_ball_subset (x : ℝ × ℝ) (hx1 : 0 < x.1) (hx2 : 0 < x.2) :
    ∃ δ > 0, Metric.ball x δ ⊆ {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} := by
  refine ⟨min (x.1 / 2) (x.2 / 2), by positivity, ?_⟩
  intro z hz
  have hz' : max |z.1 - x.1| |z.2 - x.2| < min (x.1 / 2) (x.2 / 2) := by
    simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def, Real.norm_eq_abs] using hz
  have hz1 : |z.1 - x.1| < min (x.1 / 2) (x.2 / 2) := (max_lt_iff.mp hz').1
  have hz2 : |z.2 - x.2| < min (x.1 / 2) (x.2 / 2) := (max_lt_iff.mp hz').2
  constructor
  · -- The first coordinate stays above `x.1 / 2`.
    have hz1_lower : -(min (x.1 / 2) (x.2 / 2)) < z.1 - x.1 := (abs_lt.mp hz1).1
    have hδx1 : min (x.1 / 2) (x.2 / 2) ≤ x.1 / 2 := min_le_left _ _
    nlinarith
  · -- The second coordinate stays above `x.2 / 2`.
    have hz2_lower : -(min (x.1 / 2) (x.2 / 2)) < z.2 - x.2 := (abs_lt.mp hz2).1
    have hδx2 : min (x.1 / 2) (x.2 / 2) ≤ x.2 / 2 := min_le_right _ _
    nlinarith

/-- Helper for Example 10.19: on the positive orthant, the explicit `EReal` formula is
continuous because it agrees locally with its finite real branch. -/
private theorem continuousAt_example10_19Function_asEReal_of_pos (x : ℝ × ℝ)
    (hx1 : 0 < x.1) (hx2 : 0 < x.2) :
    ContinuousAt example10_19Function.asEReal x := by
  rcases positiveOrthant_ball_subset x hx1 hx2 with ⟨δ, hδ, hball⟩
  have hEq :
      example10_19Function.asEReal =ᶠ[nhds x]
        fun z ↦ ((positiveBranchFormula z : ℝ) : EReal) := by
    -- Inside the small positive ball, the `EReal` function is exactly the finite branch.
    change {z | example10_19Function.asEReal z = ((positiveBranchFormula z : ℝ) : EReal)} ∈
      nhds x
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x hδ) ?_
    intro z hz
    exact positiveBranchFormula_eq z (hball hz)
  rw [continuousAt_congr hEq]
  have hsq : ContinuousAt (fun z : ℝ × ℝ ↦ z.2 ^ (2 : ℕ)) x := by
    simpa using
      (continuous_snd.continuousAt.pow (2 : ℕ) :
        ContinuousAt (fun z : ℝ × ℝ ↦ z.2 ^ (2 : ℕ)) x)
  have hdiv : ContinuousAt (fun z : ℝ × ℝ ↦ z.2 ^ (2 : ℕ) / (2 * z.1)) x := by
    -- The denominator does not vanish at a positive point.
    refine hsq.div ?_ ?_
    · simpa using
        ((continuous_fst.const_mul (2 : ℝ)).continuousAt :
          ContinuousAt (fun z : ℝ × ℝ ↦ 2 * z.1) x)
    nlinarith
  have hbranch : ContinuousAt positiveBranchFormula x := by
    -- The positive branch is the sum of the rational term and the square term.
    simpa [positiveBranchFormula] using hdiv.add hsq
  exact continuous_coe_real_ereal.continuousAt.comp hbranch

/-- Helper for Example 10.19: the restriction is lower semicontinuous at the singular origin
because every point of `C` lies in the nonnegative effective domain. -/
private theorem origin_lowerSemicontinuousWithinAt_example10_19Set (ρ : Set.Ioi (0 : ℝ)) :
    LowerSemicontinuousWithinAt example10_19Function.asEReal (example10_19Set ρ) (0, 0) := by
  rw [lowerSemicontinuousWithinAt_iff]
  intro y hy
  have hy0 : y < (0 : EReal) := by
    simpa [example10_19Function_apply, example10_19FunctionEReal] using hy
  -- Every point of `C` lies in the effective domain, where the function is nonnegative.
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzdom : z ∈ effectiveDomain example10_19Function :=
    hz.2
  have hnonneg : (0 : EReal) ≤ example10_19Function.asEReal z :=
    example10_19Function_nonneg_of_mem_effectiveDomain z hzdom
  exact lt_of_lt_of_le hy0 hnonneg

section Statements

variable (ρ : Set.Ioi (0 : ℝ))

-- Proof sketch: analyze the explicit formula on the positive orthant, where the Hessian is
-- positive definite, and note that the value `⊤` outside the effective domain forces the strict
-- Jensen inequality whenever one endpoint leaves the domain.
/-- Clause (1) of Example 10.19: the explicit function on `ℝ²` is strictly convex. -/
theorem example10_19Function_strictlyConvex :
    StrictlyConvex example10_19Function := by
  intro x hx y hy hxy α hα0 hα1
  have hβ : 0 < 1 - α := by
    linarith
  have hzero :
      ((example10_19Function (0, 0) : Set.Ioi (⊥ : EReal)) : EReal) = 0 := by
    simp [example10_19Function_apply, example10_19FunctionEReal]
  rcases (mem_effectiveDomain_example10_19Function_iff x).1 hx with rfl | hxpos
  · rcases (mem_effectiveDomain_example10_19Function_iff y).1 hy with rfl | hypos
    · exact (hxy rfl).elim
    · have hcombo_pos : 0 < ((1 - α) • y).1 ∧ 0 < ((1 - α) • y).2 := by
        constructor
        · change 0 < (1 - α) * y.1
          nlinarith [hβ, hypos.1]
        · change 0 < (1 - α) * y.2
          nlinarith [hβ, hypos.2]
      have hcombo_eq : α • ((0, 0) : ℝ × ℝ) + (1 - α) • y = (1 - α) • y := by
        ext <;> simp [Prod.smul_mk]
      have hcombo_val :
          ((example10_19Function ((1 - α) • y) : Set.Ioi (⊥ : EReal)) : EReal) =
            ((positiveBranchFormula ((1 - α) • y) : ℝ) : EReal) := by
        simpa [Function.asEReal_apply] using positiveBranchFormula_eq ((1 - α) • y) hcombo_pos
      have hy_val :
          ((example10_19Function y : Set.Ioi (⊥ : EReal)) : EReal) =
            ((positiveBranchFormula y : ℝ) : EReal) := by
        simpa [Function.asEReal_apply] using positiveBranchFormula_eq y hypos
      rw [hcombo_eq, hcombo_val, hzero, mul_zero, zero_add, hy_val]
      have hβ_cast : (1 - α : EReal) = (((1 - α : ℝ)) : EReal) := by
        exact_mod_cast rfl
      rw [hβ_cast, ← EReal.coe_mul]
      exact EReal.coe_lt_coe_iff.mpr <|
        positiveBranchRayStrict (β := 1 - α) hβ (by linarith) hypos.1 hypos.2
  · rcases (mem_effectiveDomain_example10_19Function_iff y).1 hy with rfl | hypos
    · have hcombo_pos : 0 < (α • x).1 ∧ 0 < (α • x).2 := by
        constructor
        · change 0 < α * x.1
          nlinarith [hα0, hxpos.1]
        · change 0 < α * x.2
          nlinarith [hα0, hxpos.2]
      have hcombo_eq : α • x + (1 - α) • ((0, 0) : ℝ × ℝ) = α • x := by
        ext <;> simp [Prod.smul_mk]
      have hcombo_val :
          ((example10_19Function (α • x) : Set.Ioi (⊥ : EReal)) : EReal) =
            ((positiveBranchFormula (α • x) : ℝ) : EReal) := by
        simpa [Function.asEReal_apply] using positiveBranchFormula_eq (α • x) hcombo_pos
      have hx_val :
          ((example10_19Function x : Set.Ioi (⊥ : EReal)) : EReal) =
            ((positiveBranchFormula x : ℝ) : EReal) := by
        simpa [Function.asEReal_apply] using positiveBranchFormula_eq x hxpos
      rw [hcombo_eq, hcombo_val, hx_val, hzero, mul_zero, add_zero, ← EReal.coe_mul]
      exact EReal.coe_lt_coe_iff.mpr <|
        positiveBranchRayStrict (β := α) hα0 hα1 hxpos.1 hxpos.2
    · exact strictJensen_positiveOrthant hxpos hypos hxy hα0 hα1

-- Proof sketch: since `ρ > 0`, the origin belongs to the open ball of radius `ρ`; the defining
-- formula gives the finite value `0` at the origin, so `0 ∈ C`.
/-- Clause (2) of Example 10.19: for every positive radius `ρ`, the set `C = B(0;ρ) ∩ dom f`
is nonempty. -/
theorem example10_19Set_nonempty :
    (example10_19Set ρ).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  -- The origin lies in both the ball of radius `ρ` and the effective domain.
  rw [mem_example10_19Set_iff]
  constructor
  · simpa using (show (0 : ℝ) < (ρ : ℝ) from ρ.2)
  · exact Or.inl rfl

-- Proof sketch: `example10_19Set ρ` is contained in the open ball `B(0; ρ)`, and every metric
-- ball in a normed space is bounded.
/-- Clause (3) of Example 10.19: for every positive radius `ρ`, the set `C = B(0;ρ) ∩ dom f`
is bounded. -/
theorem example10_19Set_bounded :
    Bornology.IsBounded (example10_19Set ρ) := by
  -- The set is contained in the ambient metric ball.
  exact Bornology.IsBounded.subset Metric.isBounded_ball fun _ hx ↦ hx.1

-- Proof sketch: identify `dom f` with `{(ξ, η) | ξ = 0 ∧ η = 0} ∪ {(ξ, η) | 0 < ξ ∧ 0 < η}` and
-- verify that this domain is convex; then intersect with the convex ball `B(0; ρ)`.
/-- Clause (4) of Example 10.19: for every positive radius `ρ`, the set `C = B(0;ρ) ∩ dom f`
is convex. -/
theorem example10_19Set_convex :
    Convex ℝ (example10_19Set ρ) := by
  -- Intersect the convex ball with the already-convex effective domain.
  exact (convex_ball (0 : ℝ × ℝ) (ρ : ℝ)).inter effectiveDomain_example10_19Function_convex

-- Proof sketch: this is immediate from the definition `C = B(0; ρ) ∩ dom f`.
/-- Clause (5) of Example 10.19: for every positive radius `ρ`, the set
`C = B(0;ρ) ∩ dom f` is contained
in `dom f`. -/
theorem example10_19Set_subset_effectiveDomain :
    example10_19Set ρ ⊆ effectiveDomain example10_19Function := by
  -- This is the second projection of the defining intersection.
  intro x hx
  exact hx.2

-- Proof sketch: restrict the global strict convexity from clause (1) to the subset `C`.
/-- Clause (6) of Example 10.19: for every positive radius `ρ`, the function is strictly convex on
`C = B(0;ρ) ∩ dom f`. -/
theorem example10_19Function_strictlyConvexOn_set :
    StrictlyConvexOn example10_19Function (example10_19Set ρ) := by
  -- Restrict the global strict convexity to the nonempty subset `C`.
  exact example10_19Function_strictlyConvex.strictlyConvexOn
    (example10_19Set_nonempty (ρ := ρ))
    (example10_19Set_subset_effectiveDomain (ρ := ρ))

-- Proof sketch: on `C` the function is finite and given by a continuous real formula on the
-- positive-orthant branch together with the value `0` at the origin, so the restricted `EReal`
-- function is lower semicontinuous on `C`.
/-- Example 10.19 (7): for every positive radius `ρ`, the restriction of the function to
`C = B(0;ρ) ∩ dom f` is lower semicontinuous. -/
theorem example10_19Function_restriction_lowerSemicontinuous :
    LowerSemicontinuousOn example10_19Function.asEReal (example10_19Set ρ) := by
  rw [lowerSemicontinuousOn_iff]
  intro x hx
  rcases (mem_example10_19Set_iff ρ x).1 hx with ⟨_, rfl | hxpos⟩
  · -- At the origin, lower semicontinuity comes from the global nonnegativity on `C`.
    simpa using origin_lowerSemicontinuousWithinAt_example10_19Set (ρ := ρ)
  · -- Away from the origin, the function is locally the continuous positive branch.
    have hcont :
        ContinuousWithinAt example10_19Function.asEReal (example10_19Set ρ) x :=
      (continuousAt_example10_19Function_asEReal_of_pos x hxpos.1 hxpos.2).continuousWithinAt
    exact hcont.lowerSemicontinuousWithinAt

-- Proof sketch: use the explicit boundary points `z_η = (√(ρ² - η²), η)` from the textbook
-- proof to show that the exact Jensen gap along the segment from `0` to `z_η` equals `η²`, which
-- tends to `0`; therefore no modulus positive away from `0` can witness uniform convexity on `C`.
/-- Clause (8) of Example 10.19: for every positive radius `ρ`, the function is not
uniformly convex on
`C = B(0;ρ) ∩ dom f`. -/
theorem example10_19Function_not_uniformlyConvexOn_set :
    ¬ ∃ φ : NNReal → EReal, UniformlyConvexOn example10_19Function (example10_19Set ρ) φ := by
  rintro ⟨φ, hφ⟩
  let r : ℝ := (ρ : ℝ) / 2
  have hr : 0 < r := by
    have hr' : 0 < (ρ : ℝ) / 2 := half_pos ρ.2
    simpa [r] using hr'
  have hrρ : r < (ρ : ℝ) := by
    have hrρ' : (ρ : ℝ) / 2 < (ρ : ℝ) := half_lt_self ρ.2
    simpa [r] using hrρ'
  let rr : NNReal := ⟨r, hr.le⟩
  have hrr_ne : rr ≠ 0 := by
    intro hrr
    have : r = 0 := by
      exact congrArg (fun t : NNReal ↦ (t : ℝ)) hrr
    exact hr.ne' this
  have hzero_mem : (0, 0) ∈ example10_19Set ρ := by
    rw [mem_example10_19Set_iff]
    constructor
    · simpa using (show (0 : ℝ) < (ρ : ℝ) from ρ.2)
    · exact Or.inl rfl
  have hφrr_zero : φ rr = 0 := by
    by_contra hφrr_nonzero
    let term : EReal := (((1 / 4 : ℝ) : EReal) * φ rr)
    have hφrr_nonneg : 0 ≤ φ rr := by
      rw [← (hφ.modulus_eq_zero_iff 0).2 rfl]
      exact hφ.monotone (show (0 : NNReal) ≤ rr by exact rr.2)
    have hφrr_pos : (0 : EReal) < φ rr :=
      lt_of_le_of_ne hφrr_nonneg (Ne.symm hφrr_nonzero)
    have hterm_pos : (0 : EReal) < term := by
      have hquarter_pos : (0 : EReal) < (((1 / 4 : ℝ) : EReal)) := by
        exact_mod_cast (show 0 < (1 / 4 : ℝ) by norm_num)
      simpa [term] using EReal.mul_pos hquarter_pos hφrr_pos
    have hterm_bot : term ≠ ⊥ := by
      intro hbot
      simp [term, hbot] at hterm_pos
    let η₀ : ℝ := r / 2
    have hη₀_pos : 0 < η₀ := by
      dsimp [η₀]
      nlinarith [hr]
    have hη₀_lt : η₀ < r := by
      dsimp [η₀]
      nlinarith [hr]
    have hbound₀ :
        term ≤ (((η₀ ^ (2 : ℕ)) / 4 : ℝ) : EReal) := by
      have hgap :=
        hφ.gap_le
          (x := (r, η₀)) (innerPoint_mem_set (ρ := ρ) hr hrρ hη₀_pos hη₀_lt)
          (y := (0, 0)) hzero_mem
          (α := (1 / 2 : ℝ)) (hα0 := by norm_num) (hα1 := by norm_num)
      rw [innerPoint_nnnorm_eq hr hη₀_pos hη₀_lt, innerPoint_gap_eq hr hη₀_pos] at hgap
      norm_num [term] at hgap
      simpa [term] using hgap
    have hterm_top : term ≠ ⊤ := by
      exact ne_of_lt <| lt_of_le_of_lt hbound₀ (EReal.coe_lt_top _)
    have hterm_toReal_pos : 0 < term.toReal := by
      have hcoe : ((term.toReal : ℝ) : EReal) = term := EReal.coe_toReal hterm_top hterm_bot
      have : (0 : EReal) < ((term.toReal : ℝ) : EReal) := by
        simpa [hcoe] using hterm_pos
      exact_mod_cast this
    let η : ℝ := min (r / 2) (min 1 term.toReal)
    have hη_pos : 0 < η := by
      dsimp [η]
      refine lt_min ?_ ?_
      · nlinarith [hr]
      · exact lt_min (by norm_num) hterm_toReal_pos
    have hη_lt : η < r := by
      dsimp [η]
      have hη_le : η ≤ r / 2 := min_le_left _ _
      nlinarith [hr, hη_le]
    have hη_le_one : η ≤ 1 := by
      dsimp [η]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hη_le_term : η ≤ term.toReal := by
      dsimp [η]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hsq_le : η ^ (2 : ℕ) / 4 ≤ η / 4 := by
      nlinarith [le_of_lt hη_pos, hη_le_one]
    have hquarter_lt : η / 4 < η := by
      nlinarith [hη_pos]
    have hsmall : η ^ (2 : ℕ) / 4 < term.toReal := by
      exact lt_of_le_of_lt hsq_le (lt_of_lt_of_le hquarter_lt hη_le_term)
    have hbound :
        term ≤ (((η ^ (2 : ℕ)) / 4 : ℝ) : EReal) := by
      have hgap :=
        hφ.gap_le
          (x := (r, η)) (innerPoint_mem_set (ρ := ρ) hr hrρ hη_pos hη_lt)
          (y := (0, 0)) hzero_mem
          (α := (1 / 2 : ℝ)) (hα0 := by norm_num) (hα1 := by norm_num)
      rw [innerPoint_nnnorm_eq hr hη_pos hη_lt, innerPoint_gap_eq hr hη_pos] at hgap
      norm_num [term] at hgap
      simpa [term] using hgap
    have hbound_real : term.toReal ≤ η ^ (2 : ℕ) / 4 := by
      exact EReal.toReal_le_toReal hbound hterm_bot (EReal.coe_ne_top _)
    exact (not_lt_of_ge hbound_real) hsmall
  exact hrr_ne ((hφ.modulus_eq_zero_iff rr).1 hφrr_zero)

end Statements

end ERealFunction
