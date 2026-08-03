module

public import Topology_Munkres_2000.Book.Theorem_18_3
public import Mathlib.Topology.Algebra.Ring.Real

public section

/-- The function obtained by pasting `x` and `x / 2` along the closed half-lines meeting at
zero. -/
noncomputable def closedPastingMap (x : ℝ) : ℝ := if x ≤ 0 then x else x / 2

/-- On the nonpositive half-line, `closedPastingMap` is the identity. -/
@[simp]
theorem closedPastingMap_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    closedPastingMap x = x := by
  simp [closedPastingMap, hx]

/-- On the nonnegative half-line, `closedPastingMap` is division by two. -/
@[simp]
theorem closedPastingMap_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    closedPastingMap x = x / 2 := by
  by_cases h : x ≤ 0
  · have hx0 : x = 0 := le_antisymm h hx
    subst x
    simp [closedPastingMap]
  · simp [closedPastingMap, h]

/-- Example 18.8 (1): the two continuous formulas defining `closedPastingMap` agree at zero,
so their pasting along the closed half-lines is continuous. -/
theorem closedPastingMap_continuous : Continuous closedPastingMap := by
  -- Restrict the two continuous formulas to the closed half-lines.
  let f : ContinuousMap (Set.Iic (0 : ℝ)) ℝ := (ContinuousMap.id ℝ).restrict _
  let g : ContinuousMap (Set.Ici (0 : ℝ)) ℝ :=
    ⟨fun x ↦ (x : ℝ) / 2, continuous_subtype_val.div_const 2⟩
  -- On the overlap both subtype values are zero, so the formulas agree.
  have hfg : ∀ x : (Set.Iic (0 : ℝ) ∩ Set.Ici 0 : Set ℝ),
      f ⟨x, x.property.1⟩ = g ⟨x, x.property.2⟩ := by
    intro x
    have hx : (x : ℝ) = 0 := le_antisymm x.property.1 x.property.2
    calc
      f ⟨x, x.property.1⟩ = (x : ℝ) := rfl
      _ = (x : ℝ) / 2 := by
        rw [hx]
        norm_num
      _ = g ⟨x, x.property.2⟩ := rfl
  obtain ⟨h, hnonpos, hnonneg⟩ := existsContinuousMap_of_isClosed_cover
    isClosed_Iic isClosed_Ici Set.Iic_union_Ici f g hfg
  -- Identify the pasted map with the explicit piecewise function on each half-line.
  refine h.continuous.congr ?_
  intro x
  by_cases hx : x ≤ 0
  · calc
      h x = f ⟨x, hx⟩ := hnonpos ⟨x, hx⟩
      _ = x := rfl
      _ = closedPastingMap x := (closedPastingMap_of_nonpos hx).symm
  · have hxpos : 0 ≤ x := le_of_lt (lt_of_not_ge hx)
    calc
      h x = g ⟨x, hxpos⟩ := hnonneg ⟨x, hxpos⟩
      _ = x / 2 := rfl
      _ = closedPastingMap x := (closedPastingMap_of_nonneg hxpos).symm

/-- Example 18.8 (2): the formulas `x - 2` on `x ≤ 0` and `x + 2` on `0 ≤ x` do not define
a function because they prescribe incompatible values at zero. -/
theorem incompatibleClosedPieces_no_function :
    ¬ ∃ k : ℝ → ℝ, (∀ x, x ≤ 0 → k x = x - 2) ∧ (∀ x, 0 ≤ x → k x = x + 2) := by
  -- Evaluating both prescriptions at the common endpoint forces unequal values for `k 0`.
  rintro ⟨k, hnonpos, hnonneg⟩
  have hleft := hnonpos 0 le_rfl
  have hright := hnonneg 0 le_rfl
  linarith

/-- The function obtained from `x - 2` on the negative half-line and `x + 2` on the
nonnegative half-line. -/
noncomputable def halfOpenJumpMap (x : ℝ) : ℝ := if x < 0 then x - 2 else x + 2

/-- On the negative half-line, `halfOpenJumpMap` is translation by `-2`. -/
@[simp]
theorem halfOpenJumpMap_of_neg {x : ℝ} (hx : x < 0) :
    halfOpenJumpMap x = x - 2 := by
  simp [halfOpenJumpMap, hx]

/-- On the nonnegative half-line, `halfOpenJumpMap` is translation by `2`. -/
@[simp]
theorem halfOpenJumpMap_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    halfOpenJumpMap x = x + 2 := by
  simp [halfOpenJumpMap, hx.not_gt]

/-- Example 18.8 (3): the inverse image of `(1, 3)` under `halfOpenJumpMap` is `[0, 1)`. -/
theorem halfOpenJumpMap_preimage_Ioo :
    halfOpenJumpMap ⁻¹' Set.Ioo (1 : ℝ) 3 = Set.Ico 0 1 := by
  -- Compute membership separately on the negative and nonnegative branches.
  ext x
  simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_Ico]
  by_cases hx : x < 0
  · rw [halfOpenJumpMap_of_neg hx]
    constructor
    · intro h
      linarith
    · intro h
      linarith
  · have hxnonneg : 0 ≤ x := le_of_not_gt hx
    rw [halfOpenJumpMap_of_nonneg hxnonneg]
    constructor
    · intro h
      constructor
      · exact hxnonneg
      · linarith
    · intro h
      constructor
      · linarith
      · linarith

/-- Helper for Example 18.8: the real half-open interval `[0, 1)` is not open. -/
private lemma not_isOpen_Ico_zero_one : ¬ IsOpen (Set.Ico (0 : ℝ) 1) := by
  -- An open set equals its interior, but the interior of `[0, 1)` omits zero.
  intro hopen
  have hinterior := hopen.interior_eq
  rw [interior_Ico] at hinterior
  have hzero : (0 : ℝ) ∈ Set.Ico 0 1 := by
    constructor
    · exact le_rfl
    · norm_num
  rw [← hinterior] at hzero
  exact (lt_irrefl 0) hzero.1

/-- Example 18.8 (4): although each branch is continuous, `halfOpenJumpMap` is not
continuous. -/
theorem halfOpenJumpMap_not_continuous : ¬ Continuous halfOpenJumpMap := by
  -- Continuity would make the computed preimage of `(1, 3)` open.
  intro hcontinuous
  apply not_isOpen_Ico_zero_one
  rw [← halfOpenJumpMap_preimage_Ioo]
  exact hcontinuous.isOpen_preimage _ isOpen_Ioo
