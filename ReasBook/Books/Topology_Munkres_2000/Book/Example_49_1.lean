import Topology_Munkres_2000.Book.Example_49_1.LargeSecants

open Set
open scoped UnitIntervalSecant

namespace UnitIntervalSecant

/-- The parabolic function `x ↦ 4 * α * x * (1 - x)` from Example 49.1. -/
def parabolicExample (α : ℝ) : C(unitInterval, ℝ) where
  toFun x := 4 * α * (x : ℝ) * (1 - (x : ℝ))
  continuous_toFun :=
    (continuous_const.mul continuous_subtype_val).mul
      (continuous_const.sub continuous_subtype_val)

/-- Evaluation of the parabolic function from Example 49.1. -/
theorem parabolicExample_apply (α : ℝ) (x : unitInterval) :
    parabolicExample α x = 4 * α * (x : ℝ) * (1 - (x : ℝ)) := rfl

/-- The triangular function of height `α / 2` pictured in Figure 49.1. -/
def tentExample (α : ℝ) : C(unitInterval, ℝ) where
  toFun x := α * min (x : ℝ) (1 - (x : ℝ))
  continuous_toFun := continuous_const.mul
    (continuous_subtype_val.min (continuous_const.sub continuous_subtype_val))

/-- Evaluation of the triangular function from Figure 49.1. -/
theorem tentExample_apply (α : ℝ) (x : unitInterval) :
    tentExample α x = α * min (x : ℝ) (1 - (x : ℝ)) := rfl

/-- The double-triangular function of height `α / 4` pictured in Figure 49.1. -/
noncomputable def doubleTentExample (α : ℝ) : C(unitInterval, ℝ) where
  toFun x := α * min (x : ℝ) (min |(x : ℝ) - 1 / 2| (1 - (x : ℝ)))
  continuous_toFun := continuous_const.mul <|
    continuous_subtype_val.min <|
      (continuous_subtype_val.sub continuous_const).abs.min
        (continuous_const.sub continuous_subtype_val)

/-- Evaluation of the double-triangular function from Figure 49.1. -/
theorem doubleTentExample_apply (α : ℝ) (x : unitInterval) :
    doubleTentExample α x =
      α * min (x : ℝ) (min |(x : ℝ) - 1 / 2| (1 - (x : ℝ))) := rfl

/-- Helper for Example 49.1: in a closed interval of width at least `2 * h`,
one of the two points at distance `h` from a given point remains in the interval. -/
private lemma add_mem_Icc_or_sub_mem_Icc {a b x h : ℝ} (hx : x ∈ Icc a b)
    (hpos : 0 < h) (hwidth : 2 * h ≤ b - a) :
    x + h ∈ Icc a b ∨ x - h ∈ Icc a b := by
  -- If the right endpoint leaves the interval, the width bound forces the left one inside.
  by_cases hright : x + h ≤ b
  · left
    constructor
    · linarith [hx.1]
    · exact hright
  · right
    constructor
    · linarith [hx.2]
    · linarith [hx.2]

/-- Helper for Example 49.1: a uniform pointwise secant bound yields membership
in `U_{n}` at any admissible scale. -/
private lemma mem_largeSecantSet_of_uniformLowerBound {f : C(unitInterval, ℝ)}
    {n : ℕ} {α h : ℝ} (hpos : 0 < h) (hnscale : h ≤ 1 / (n : ℝ))
    (hhalf : h ≤ 1 / 2) (hnα : (n : ℝ) < α)
    (hlower : ∀ x, α ≤ Δ f (x, h)) :
    f ∈ U_{n} := by
  -- Pass the pointwise estimate through the infimum, then use the defining witness for `U_{n}`.
  have hinf : α ≤ Δ_{h} f :=
    (le_infMagnitude_iff f h hpos hhalf).mpr hlower
  rw [mem_largeSecantSet]
  exact ⟨h, hpos, hnscale, hnα.trans_le hinf⟩

/-- Example 49.1 (1): at scale `1 / 4`, every point of the parabola has an
available secant whose slope magnitude is at least `α`. -/
theorem parabolicExample_largeSecant (α : ℝ) (x : unitInterval) :
    α ≤ Δ (parabolicExample α) (x, 1 / 4) := by
  -- Nonpositive lower bounds follow from nonnegativity of every available magnitude.
  by_cases hαnonpos : α ≤ 0
  · have hquarterPos : (0 : ℝ) < 1 / 4 := by norm_num
    have hquarterHalf : (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
    exact hαnonpos.trans
      (maxMagnitude_nonneg (parabolicExample α) x (1 / 4) hquarterPos hquarterHalf)
  have hα : 0 < α := lt_of_not_ge hαnonpos
  rw [le_maxMagnitude_iff (parabolicExample α) hα x (1 / 4)]
  -- On each quarter interval, choose the adjacent quarter-step whose slope points away
  -- from the vertex; its linear factor has absolute value at least one.
  by_cases hquarter : (x : ℝ) ≤ 1 / 4
  · have hyMem : (x : ℝ) + 1 / 4 ∈ Icc (0 : ℝ) 1 := by
      constructor
      · linarith [x.property.1]
      · linarith
    have hfactor : 1 ≤ 3 - 8 * (x : ℝ) := by linarith
    have hnonneg : 0 ≤ α * (3 - 8 * (x : ℝ)) :=
      mul_nonneg hα.le (le_trans zero_le_one hfactor)
    left
    refine ⟨⟨(x : ℝ) + 1 / 4, hyMem⟩, rfl, ?_⟩
    rw [parabolicExample_apply, parabolicExample_apply]
    have hslope :
        (4 * α * ((x : ℝ) + 1 / 4) * (1 - ((x : ℝ) + 1 / 4)) -
          4 * α * (x : ℝ) * (1 - (x : ℝ))) / (1 / 4) =
            α * (3 - 8 * (x : ℝ)) := by
      ring
    calc
      α ≤ α * (3 - 8 * (x : ℝ)) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor hα.le
      _ = |(4 * α * ((x : ℝ) + 1 / 4) * (1 - ((x : ℝ) + 1 / 4)) -
          4 * α * (x : ℝ) * (1 - (x : ℝ))) / (1 / 4)| := by
        rw [hslope, abs_of_nonneg hnonneg]
  · by_cases hhalf : (x : ℝ) ≤ 1 / 2
    · have hyMem : (x : ℝ) - 1 / 4 ∈ Icc (0 : ℝ) 1 := by
        constructor
        · linarith
        · linarith [x.property.2]
      have hfactor : 1 ≤ 5 - 8 * (x : ℝ) := by linarith
      have hnonneg : 0 ≤ α * (5 - 8 * (x : ℝ)) :=
        mul_nonneg hα.le (le_trans zero_le_one hfactor)
      right
      refine ⟨⟨(x : ℝ) - 1 / 4, hyMem⟩, rfl, ?_⟩
      rw [parabolicExample_apply, parabolicExample_apply]
      have hslope :
          (4 * α * ((x : ℝ) - 1 / 4) * (1 - ((x : ℝ) - 1 / 4)) -
            4 * α * (x : ℝ) * (1 - (x : ℝ))) / (-(1 / 4)) =
              α * (5 - 8 * (x : ℝ)) := by
        ring
      calc
        α ≤ α * (5 - 8 * (x : ℝ)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor hα.le
        _ = |(4 * α * ((x : ℝ) - 1 / 4) * (1 - ((x : ℝ) - 1 / 4)) -
            4 * α * (x : ℝ) * (1 - (x : ℝ))) / (-(1 / 4))| := by
          rw [hslope, abs_of_nonneg hnonneg]
    · by_cases hthreequarters : (x : ℝ) ≤ 3 / 4
      · have hyMem : (x : ℝ) + 1 / 4 ∈ Icc (0 : ℝ) 1 := by
          constructor
          · linarith [x.property.1]
          · linarith
        have hfactor : 3 - 8 * (x : ℝ) ≤ -1 := by linarith
        have hproduct : α * (3 - 8 * (x : ℝ)) ≤ α * (-1) :=
          mul_le_mul_of_nonneg_left hfactor hα.le
        have hnonpos : α * (3 - 8 * (x : ℝ)) ≤ 0 := by linarith
        left
        refine ⟨⟨(x : ℝ) + 1 / 4, hyMem⟩, rfl, ?_⟩
        rw [parabolicExample_apply, parabolicExample_apply]
        have hslope :
            (4 * α * ((x : ℝ) + 1 / 4) * (1 - ((x : ℝ) + 1 / 4)) -
              4 * α * (x : ℝ) * (1 - (x : ℝ))) / (1 / 4) =
                α * (3 - 8 * (x : ℝ)) := by
          ring
        calc
          α ≤ -(α * (3 - 8 * (x : ℝ))) := by linarith
          _ = |(4 * α * ((x : ℝ) + 1 / 4) * (1 - ((x : ℝ) + 1 / 4)) -
              4 * α * (x : ℝ) * (1 - (x : ℝ))) / (1 / 4)| := by
            rw [hslope, abs_of_nonpos hnonpos]
      · have hyMem : (x : ℝ) - 1 / 4 ∈ Icc (0 : ℝ) 1 := by
          constructor
          · linarith [x.property.1]
          · linarith [x.property.2]
        have hfactor : 5 - 8 * (x : ℝ) ≤ -1 := by linarith
        have hproduct : α * (5 - 8 * (x : ℝ)) ≤ α * (-1) :=
          mul_le_mul_of_nonneg_left hfactor hα.le
        have hnonpos : α * (5 - 8 * (x : ℝ)) ≤ 0 := by linarith
        right
        refine ⟨⟨(x : ℝ) - 1 / 4, hyMem⟩, rfl, ?_⟩
        rw [parabolicExample_apply, parabolicExample_apply]
        have hslope :
            (4 * α * ((x : ℝ) - 1 / 4) * (1 - ((x : ℝ) - 1 / 4)) -
              4 * α * (x : ℝ) * (1 - (x : ℝ))) / (-(1 / 4)) =
                α * (5 - 8 * (x : ℝ)) := by
          ring
        calc
          α ≤ -(α * (5 - 8 * (x : ℝ))) := by linarith
          _ = |(4 * α * ((x : ℝ) - 1 / 4) * (1 - ((x : ℝ) - 1 / 4)) -
              4 * α * (x : ℝ) * (1 - (x : ℝ))) / (-(1 / 4))| := by
            rw [hslope, abs_of_nonpos hnonpos]

/-- Example 49.1 (2): when `α > 4`, the parabolic example belongs to `U₄`. -/
theorem parabolicExample_mem_u4 {α : ℝ} (hα : 4 < α) :
    parabolicExample α ∈ U_{4} := by
  -- Use the quarter-scale pointwise theorem as the uniform infimum bound.
  have hquarterPos : (0 : ℝ) < 1 / 4 := by norm_num
  have hquarterScale : (1 / 4 : ℝ) ≤ 1 / (4 : ℝ) := by norm_num
  have hquarterHalf : (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
  exact mem_largeSecantSet_of_uniformLowerBound hquarterPos hquarterScale hquarterHalf hα
    (parabolicExample_largeSecant α)

/-- Example 49.1 (3): at every positive scale at most `1 / 4`, every point of
the triangular example has an available secant of slope magnitude at least `α`. -/
theorem tentExample_largeSecant (α : ℝ) {h : ℝ} (hpos : 0 < h)
    (hle : h ≤ 1 / 4) (x : unitInterval) :
    α ≤ Δ (tentExample α) (x, h) := by
  have hhalfScale : h ≤ 1 / 2 := by linarith
  -- As for the parabola, only the positive-`α` branch requires a concrete endpoint.
  by_cases hαnonpos : α ≤ 0
  · exact hαnonpos.trans
      (maxMagnitude_nonneg (tentExample α) x h hpos hhalfScale)
  have hα : 0 < α := lt_of_not_ge hαnonpos
  rw [le_maxMagnitude_iff (tentExample α) hα x h]
  by_cases hxhalf : (x : ℝ) ≤ 1 / 2
  · have hxcell : (x : ℝ) ∈ Icc (0 : ℝ) (1 / 2) :=
      ⟨x.property.1, hxhalf⟩
    have hwidth : 2 * h ≤ (1 / 2 : ℝ) - 0 := by linarith
    have hformula (z : unitInterval) (hz : (z : ℝ) ∈ Icc (0 : ℝ) (1 / 2)) :
        tentExample α z = α * (z : ℝ) := by
      have hmin : (z : ℝ) ≤ 1 - (z : ℝ) := by linarith [hz.2]
      rw [tentExample_apply, min_eq_left hmin]
    -- Keep the second endpoint in the increasing affine half.
    rcases add_mem_Icc_or_sub_mem_Icc hxcell hpos hwidth with hyplus | hyminus
    · left
      have hyplusUnit : (x : ℝ) + h ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact hyplus.1
        · linarith [hyplus.2]
      refine ⟨⟨(x : ℝ) + h, hyplusUnit⟩, rfl, ?_⟩
      rw [hformula _ hyplus, hformula x hxcell]
      have hslope :
          (α * ((x : ℝ) + h) - α * (x : ℝ)) / h = α := by
        field_simp [hpos.ne']
        ring
      rw [hslope, abs_of_nonneg hα.le]
    · right
      have hyminusUnit : (x : ℝ) - h ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact hyminus.1
        · linarith [hyminus.2]
      refine ⟨⟨(x : ℝ) - h, hyminusUnit⟩, rfl, ?_⟩
      rw [hformula _ hyminus, hformula x hxcell]
      have hslope :
          (α * ((x : ℝ) - h) - α * (x : ℝ)) / (-h) = α := by
        field_simp [hpos.ne']
        ring
      rw [hslope, abs_of_nonneg hα.le]
  · have hxcell : (x : ℝ) ∈ Icc (1 / 2 : ℝ) 1 :=
      ⟨(lt_of_not_ge hxhalf).le, x.property.2⟩
    have hwidth : 2 * h ≤ (1 : ℝ) - 1 / 2 := by linarith
    have hformula (z : unitInterval) (hz : (z : ℝ) ∈ Icc (1 / 2 : ℝ) 1) :
        tentExample α z = α * (1 - (z : ℝ)) := by
      have hmin : 1 - (z : ℝ) ≤ (z : ℝ) := by linarith [hz.1]
      rw [tentExample_apply, min_eq_right hmin]
    -- Keep the second endpoint in the decreasing affine half.
    rcases add_mem_Icc_or_sub_mem_Icc hxcell hpos hwidth with hyplus | hyminus
    · left
      have hyplusUnit : (x : ℝ) + h ∈ Icc (0 : ℝ) 1 := by
        constructor
        · linarith [hyplus.1]
        · exact hyplus.2
      refine ⟨⟨(x : ℝ) + h, hyplusUnit⟩, rfl, ?_⟩
      rw [hformula _ hyplus, hformula x hxcell]
      have hslope :
          (α * (1 - ((x : ℝ) + h)) - α * (1 - (x : ℝ))) / h = -α := by
        field_simp [hpos.ne']
        ring
      rw [hslope, abs_neg, abs_of_nonneg hα.le]
    · right
      have hyminusUnit : (x : ℝ) - h ∈ Icc (0 : ℝ) 1 := by
        constructor
        · linarith [hyminus.1]
        · exact hyminus.2
      refine ⟨⟨(x : ℝ) - h, hyminusUnit⟩, rfl, ?_⟩
      rw [hformula _ hyminus, hformula x hxcell]
      have hslope :
          (α * (1 - ((x : ℝ) - h)) - α * (1 - (x : ℝ))) / (-h) = -α := by
        field_simp [hpos.ne']
        ring
      rw [hslope, abs_neg, abs_of_nonneg hα.le]

/-- Example 49.1 (4): the triangular example belongs to `Uₙ` whenever
`2 ≤ n < α`. -/
theorem tentExample_mem_largeSecantSet {α : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hnα : (n : ℝ) < α) :
    tentExample α ∈ U_{n} := by
  have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hdenpos : 0 < 4 * (n : ℝ) := mul_pos (by norm_num) hnpos
  have hpos : 0 < 1 / (4 * (n : ℝ)) := one_div_pos.mpr hdenpos
  have hnFour : (n : ℝ) ≤ 4 * (n : ℝ) := by nlinarith
  have hscale : 1 / (4 * (n : ℝ)) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hnpos hnFour
  have hfourDen : (4 : ℝ) ≤ 4 * (n : ℝ) := by nlinarith
  have hquarter : 1 / (4 * (n : ℝ)) ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hfourDen
  have hhalf : 1 / (4 * (n : ℝ)) ≤ (1 / 2 : ℝ) := hquarter.trans (by norm_num)
  -- Choose a scale small enough to stay in one affine cell everywhere.
  exact mem_largeSecantSet_of_uniformLowerBound hpos hscale hhalf hnα
    (tentExample_largeSecant α hpos hquarter)

/-- Example 49.1 (5): at every positive scale at most `1 / 8`, every point of
the double-triangular example has an available secant of slope magnitude at least `α`. -/
theorem doubleTentExample_largeSecant (α : ℝ) {h : ℝ} (hpos : 0 < h)
    (hle : h ≤ 1 / 8) (x : unitInterval) :
    α ≤ Δ (doubleTentExample α) (x, h) := by
  have hhalfScale : h ≤ 1 / 2 := by linarith
  -- A nonpositive lower bound again follows without choosing a secant endpoint.
  by_cases hαnonpos : α ≤ 0
  · exact hαnonpos.trans
      (maxMagnitude_nonneg (doubleTentExample α) x h hpos hhalfScale)
  have hα : 0 < α := lt_of_not_ge hαnonpos
  rw [le_maxMagnitude_iff (doubleTentExample α) hα x h]
  -- Split at the four vertices of the double tent and remain in one affine cell.
  by_cases hxquarter : (x : ℝ) ≤ 1 / 4
  · have hxcell : (x : ℝ) ∈ Icc (0 : ℝ) (1 / 4) :=
      ⟨x.property.1, hxquarter⟩
    have hwidth : 2 * h ≤ (1 / 4 : ℝ) - 0 := by linarith
    have hformula (z : unitInterval) (hz : (z : ℝ) ∈ Icc (0 : ℝ) (1 / 4)) :
        doubleTentExample α z = α * (z : ℝ) := by
      have habsNonpos : (z : ℝ) - 1 / 2 ≤ 0 := by linarith [hz.2]
      have habs : |(z : ℝ) - 1 / 2| = 1 / 2 - (z : ℝ) := by
        rw [abs_of_nonpos habsNonpos]
        ring
      have hinner : 1 / 2 - (z : ℝ) ≤ 1 - (z : ℝ) := by linarith
      have houter : (z : ℝ) ≤ 1 / 2 - (z : ℝ) := by linarith [hz.2]
      rw [doubleTentExample_apply, habs, min_eq_left hinner, min_eq_left houter]
    rcases add_mem_Icc_or_sub_mem_Icc hxcell hpos hwidth with hyplus | hyminus
    · have hyplusUnit : (x : ℝ) + h ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact hyplus.1
        · linarith [hyplus.2]
      left
      refine ⟨⟨(x : ℝ) + h, hyplusUnit⟩, rfl, ?_⟩
      rw [hformula _ hyplus, hformula x hxcell]
      have hslope :
          (α * ((x : ℝ) + h) - α * (x : ℝ)) / h = α := by
        field_simp [hpos.ne']
        ring
      rw [hslope, abs_of_nonneg hα.le]
    · have hyminusUnit : (x : ℝ) - h ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact hyminus.1
        · linarith [hyminus.2]
      right
      refine ⟨⟨(x : ℝ) - h, hyminusUnit⟩, rfl, ?_⟩
      rw [hformula _ hyminus, hformula x hxcell]
      have hslope :
          (α * ((x : ℝ) - h) - α * (x : ℝ)) / (-h) = α := by
        field_simp [hpos.ne']
        ring
      rw [hslope, abs_of_nonneg hα.le]
  · by_cases hxhalf : (x : ℝ) ≤ 1 / 2
    · have hxcell : (x : ℝ) ∈ Icc (1 / 4 : ℝ) (1 / 2) :=
        ⟨(lt_of_not_ge hxquarter).le, hxhalf⟩
      have hwidth : 2 * h ≤ (1 / 2 : ℝ) - 1 / 4 := by linarith
      have hformula (z : unitInterval)
          (hz : (z : ℝ) ∈ Icc (1 / 4 : ℝ) (1 / 2)) :
          doubleTentExample α z = α * (1 / 2 - (z : ℝ)) := by
        have habsNonpos : (z : ℝ) - 1 / 2 ≤ 0 := by linarith [hz.2]
        have habs : |(z : ℝ) - 1 / 2| = 1 / 2 - (z : ℝ) := by
          rw [abs_of_nonpos habsNonpos]
          ring
        have hinner : 1 / 2 - (z : ℝ) ≤ 1 - (z : ℝ) := by linarith
        have houter : 1 / 2 - (z : ℝ) ≤ (z : ℝ) := by linarith [hz.1]
        rw [doubleTentExample_apply, habs, min_eq_left hinner, min_eq_right houter]
      rcases add_mem_Icc_or_sub_mem_Icc hxcell hpos hwidth with hyplus | hyminus
      · have hyplusUnit : (x : ℝ) + h ∈ Icc (0 : ℝ) 1 := by
          constructor
          · linarith [hyplus.1]
          · linarith [hyplus.2]
        left
        refine ⟨⟨(x : ℝ) + h, hyplusUnit⟩, rfl, ?_⟩
        rw [hformula _ hyplus, hformula x hxcell]
        have hslope :
            (α * (1 / 2 - ((x : ℝ) + h)) - α * (1 / 2 - (x : ℝ))) / h =
              -α := by
          field_simp [hpos.ne']
          ring
        rw [hslope, abs_neg, abs_of_nonneg hα.le]
      · have hyminusUnit : (x : ℝ) - h ∈ Icc (0 : ℝ) 1 := by
          constructor
          · linarith [hyminus.1]
          · linarith [hyminus.2]
        right
        refine ⟨⟨(x : ℝ) - h, hyminusUnit⟩, rfl, ?_⟩
        rw [hformula _ hyminus, hformula x hxcell]
        have hslope :
            (α * (1 / 2 - ((x : ℝ) - h)) - α * (1 / 2 - (x : ℝ))) / (-h) =
              -α := by
          field_simp [hpos.ne']
          ring
        rw [hslope, abs_neg, abs_of_nonneg hα.le]
    · by_cases hxthreequarters : (x : ℝ) ≤ 3 / 4
      · have hxcell : (x : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 4) :=
          ⟨(lt_of_not_ge hxhalf).le, hxthreequarters⟩
        have hwidth : 2 * h ≤ (3 / 4 : ℝ) - 1 / 2 := by linarith
        have hformula (z : unitInterval)
            (hz : (z : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 4)) :
            doubleTentExample α z = α * ((z : ℝ) - 1 / 2) := by
          have habsNonneg : 0 ≤ (z : ℝ) - 1 / 2 := by linarith [hz.1]
          have hinner : (z : ℝ) - 1 / 2 ≤ 1 - (z : ℝ) := by linarith [hz.2]
          have houter : (z : ℝ) - 1 / 2 ≤ (z : ℝ) := by linarith
          rw [doubleTentExample_apply, abs_of_nonneg habsNonneg,
            min_eq_left hinner, min_eq_right houter]
        rcases add_mem_Icc_or_sub_mem_Icc hxcell hpos hwidth with hyplus | hyminus
        · have hyplusUnit : (x : ℝ) + h ∈ Icc (0 : ℝ) 1 := by
            constructor
            · linarith [hyplus.1]
            · linarith [hyplus.2]
          left
          refine ⟨⟨(x : ℝ) + h, hyplusUnit⟩, rfl, ?_⟩
          rw [hformula _ hyplus, hformula x hxcell]
          have hslope :
              (α * ((x : ℝ) + h - 1 / 2) - α * ((x : ℝ) - 1 / 2)) / h = α := by
            field_simp [hpos.ne']
            ring
          rw [hslope, abs_of_nonneg hα.le]
        · have hyminusUnit : (x : ℝ) - h ∈ Icc (0 : ℝ) 1 := by
            constructor
            · linarith [hyminus.1]
            · linarith [hyminus.2]
          right
          refine ⟨⟨(x : ℝ) - h, hyminusUnit⟩, rfl, ?_⟩
          rw [hformula _ hyminus, hformula x hxcell]
          have hslope :
              (α * ((x : ℝ) - h - 1 / 2) - α * ((x : ℝ) - 1 / 2)) / (-h) =
                α := by
            field_simp [hpos.ne']
            ring
          rw [hslope, abs_of_nonneg hα.le]
      · have hxcell : (x : ℝ) ∈ Icc (3 / 4 : ℝ) 1 :=
          ⟨(lt_of_not_ge hxthreequarters).le, x.property.2⟩
        have hwidth : 2 * h ≤ (1 : ℝ) - 3 / 4 := by linarith
        have hformula (z : unitInterval)
            (hz : (z : ℝ) ∈ Icc (3 / 4 : ℝ) 1) :
            doubleTentExample α z = α * (1 - (z : ℝ)) := by
          have habsNonneg : 0 ≤ (z : ℝ) - 1 / 2 := by linarith [hz.1]
          have hinner : 1 - (z : ℝ) ≤ (z : ℝ) - 1 / 2 := by linarith [hz.1]
          have houter : 1 - (z : ℝ) ≤ (z : ℝ) := by linarith [hz.1]
          rw [doubleTentExample_apply, abs_of_nonneg habsNonneg,
            min_eq_right hinner, min_eq_right houter]
        rcases add_mem_Icc_or_sub_mem_Icc hxcell hpos hwidth with hyplus | hyminus
        · have hyplusUnit : (x : ℝ) + h ∈ Icc (0 : ℝ) 1 := by
            constructor
            · linarith [hyplus.1]
            · exact hyplus.2
          left
          refine ⟨⟨(x : ℝ) + h, hyplusUnit⟩, rfl, ?_⟩
          rw [hformula _ hyplus, hformula x hxcell]
          have hslope :
              (α * (1 - ((x : ℝ) + h)) - α * (1 - (x : ℝ))) / h = -α := by
            field_simp [hpos.ne']
            ring
          rw [hslope, abs_neg, abs_of_nonneg hα.le]
        · have hyminusUnit : (x : ℝ) - h ∈ Icc (0 : ℝ) 1 := by
            constructor
            · linarith [hyminus.1]
            · exact hyminus.2
          right
          refine ⟨⟨(x : ℝ) - h, hyminusUnit⟩, rfl, ?_⟩
          rw [hformula _ hyminus, hformula x hxcell]
          have hslope :
              (α * (1 - ((x : ℝ) - h)) - α * (1 - (x : ℝ))) / (-h) = -α := by
            field_simp [hpos.ne']
            ring
          rw [hslope, abs_neg, abs_of_nonneg hα.le]

/-- Example 49.1 (6): the double-triangular example belongs to `Uₙ` whenever
`2 ≤ n < α`. -/
theorem doubleTentExample_mem_largeSecantSet {α : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hnα : (n : ℝ) < α) :
    doubleTentExample α ∈ U_{n} := by
  have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hdenpos : 0 < 8 * (n : ℝ) := mul_pos (by norm_num) hnpos
  have hpos : 0 < 1 / (8 * (n : ℝ)) := one_div_pos.mpr hdenpos
  have hnEight : (n : ℝ) ≤ 8 * (n : ℝ) := by nlinarith
  have hscale : 1 / (8 * (n : ℝ)) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hnpos hnEight
  have heighthDen : (8 : ℝ) ≤ 8 * (n : ℝ) := by nlinarith
  have heighth : 1 / (8 * (n : ℝ)) ≤ (1 / 8 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) heighthDen
  have hhalf : 1 / (8 * (n : ℝ)) ≤ (1 / 2 : ℝ) := heighth.trans (by norm_num)
  -- The reciprocal scale is admissible and stays inside every quarter-width affine cell.
  exact mem_largeSecantSet_of_uniformLowerBound hpos hscale hhalf hnα
    (doubleTentExample_largeSecant α hpos heighth)

end UnitIntervalSecant
