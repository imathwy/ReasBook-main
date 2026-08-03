module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Instances.AddCircle.Real

public section

namespace unitInterval

/-- The endpoint-identification relation on the closed unit interval. -/
def endpointSetoid : Setoid unitInterval :=
  Setoid.ker fun x ↦ (x : UnitAddCircle)

/-- Two points of the closed unit interval are identified exactly when they are equal or are its
two endpoints. -/
theorem endpointSetoid_iff (x y : unitInterval) :
    endpointSetoid x y ↔ x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  -- Normalize the kernel relation to equality in the additive circle.
  constructor
  · intro hxy
    change (x : UnitAddCircle) = (y : UnitAddCircle) at hxy
    have hxy_circle : (x : UnitAddCircle) = (y : UnitAddCircle) := hxy
    have hzero_mem : (0 : ℝ) ∈ Set.Ico 0 (0 + 1) := by
      norm_num
    -- The only failure of injectivity on the closed interval occurs at `1`.
    by_cases hx_one : x = 1
    · by_cases hy_one : y = 1
      · exact Or.inl (hx_one.trans hy_one.symm)
      · have hy_ne_one_real : (y : ℝ) ≠ 1 := unitInterval.coe_ne_one.mpr hy_one
        have hy_lt_one_real : (y : ℝ) < 1 :=
          lt_of_le_of_ne (unitInterval.le_one y) hy_ne_one_real
        have hy_lt_sum : (y : ℝ) < 0 + 1 := by
          simpa only [zero_add] using hy_lt_one_real
        have hy_mem : (y : ℝ) ∈ Set.Ico 0 (0 + 1) :=
          ⟨unitInterval.nonneg y, hy_lt_sum⟩
        have hy_circle_zero : (y : UnitAddCircle) = 0 := by
          calc
            (y : UnitAddCircle) = (x : UnitAddCircle) := hxy_circle.symm
            _ = ((1 : ℝ) : UnitAddCircle) :=
              congrArg (fun z : unitInterval ↦ (z : UnitAddCircle)) hx_one
            _ = 0 := AddCircle.coe_period (1 : ℝ)
        have hy_coe_zero : ((y : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := by
          calc
            ((y : ℝ) : UnitAddCircle) = 0 := hy_circle_zero
            _ = ((0 : ℝ) : UnitAddCircle) := (AddCircle.coe_zero (1 : ℝ)).symm
        have hy_val_zero : (y : ℝ) = 0 :=
          (AddCircle.coe_eq_coe_iff_of_mem_Ico hy_mem hzero_mem).mp hy_coe_zero
        have hy_zero : y = 0 := Subtype.ext hy_val_zero
        exact Or.inr (Or.inr ⟨hx_one, hy_zero⟩)
    · have hx_ne_one_real : (x : ℝ) ≠ 1 := unitInterval.coe_ne_one.mpr hx_one
      have hx_lt_one_real : (x : ℝ) < 1 :=
        lt_of_le_of_ne (unitInterval.le_one x) hx_ne_one_real
      have hx_lt_sum : (x : ℝ) < 0 + 1 := by
        simpa only [zero_add] using hx_lt_one_real
      have hx_mem : (x : ℝ) ∈ Set.Ico 0 (0 + 1) :=
        ⟨unitInterval.nonneg x, hx_lt_sum⟩
      by_cases hy_one : y = 1
      · have hx_circle_zero : (x : UnitAddCircle) = 0 := by
          calc
            (x : UnitAddCircle) = (y : UnitAddCircle) := hxy_circle
            _ = ((1 : ℝ) : UnitAddCircle) :=
              congrArg (fun z : unitInterval ↦ (z : UnitAddCircle)) hy_one
            _ = 0 := AddCircle.coe_period (1 : ℝ)
        have hx_coe_zero : ((x : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := by
          calc
            ((x : ℝ) : UnitAddCircle) = 0 := hx_circle_zero
            _ = ((0 : ℝ) : UnitAddCircle) := (AddCircle.coe_zero (1 : ℝ)).symm
        have hx_val_zero : (x : ℝ) = 0 :=
          (AddCircle.coe_eq_coe_iff_of_mem_Ico hx_mem hzero_mem).mp hx_coe_zero
        have hx_zero : x = 0 := Subtype.ext hx_val_zero
        exact Or.inr (Or.inl ⟨hx_zero, hy_one⟩)
      · have hy_ne_one_real : (y : ℝ) ≠ 1 := unitInterval.coe_ne_one.mpr hy_one
        have hy_lt_one_real : (y : ℝ) < 1 :=
          lt_of_le_of_ne (unitInterval.le_one y) hy_ne_one_real
        have hy_lt_sum : (y : ℝ) < 0 + 1 := by
          simpa only [zero_add] using hy_lt_one_real
        have hy_mem : (y : ℝ) ∈ Set.Ico 0 (0 + 1) :=
          ⟨unitInterval.nonneg y, hy_lt_sum⟩
        have hxy_val : (x : ℝ) = (y : ℝ) :=
          (AddCircle.coe_eq_coe_iff_of_mem_Ico hx_mem hy_mem).mp hxy_circle
        exact Or.inl (Subtype.ext hxy_val)
  · intro hxy
    -- Equal points map equally, while the two endpoint orders use periodicity.
    change (x : UnitAddCircle) = (y : UnitAddCircle)
    rcases hxy with hxy | hxy
    · exact congrArg (fun z : unitInterval ↦ (z : UnitAddCircle)) hxy
    · rcases hxy with hxy | hxy
      · calc
          (x : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) :=
            congrArg (fun z : unitInterval ↦ (z : UnitAddCircle)) hxy.1
          _ = 0 := AddCircle.coe_zero (1 : ℝ)
          _ = ((1 : ℝ) : UnitAddCircle) := (AddCircle.coe_period (1 : ℝ)).symm
          _ = (y : UnitAddCircle) :=
            (congrArg (fun z : unitInterval ↦ (z : UnitAddCircle)) hxy.2).symm
      · calc
          (x : UnitAddCircle) = ((1 : ℝ) : UnitAddCircle) :=
            congrArg (fun z : unitInterval ↦ (z : UnitAddCircle)) hxy.1
          _ = 0 := AddCircle.coe_period (1 : ℝ)
          _ = ((0 : ℝ) : UnitAddCircle) := (AddCircle.coe_zero (1 : ℝ)).symm
          _ = (y : UnitAddCircle) :=
            (congrArg (fun z : unitInterval ↦ (z : UnitAddCircle)) hxy.2).symm

end unitInterval

namespace TorusSquare

/-- The map from the unit square to the torus that identifies each pair of opposite edges. -/
def toTorus (point : unitInterval × unitInterval) : UnitAddCircle × UnitAddCircle :=
  (point.1, point.2)

/-- The equivalence relation on the unit square obtained by identifying opposite edges. -/
def identified : Setoid (unitInterval × unitInterval) :=
  Setoid.ker toTorus

/-- The quotient of the unit square obtained by identifying opposite edges. -/
abbrev Space := Quotient identified

/-- Two square points are identified exactly when their corresponding coordinates agree after
endpoint identification. -/
theorem identified_iff (point point' : unitInterval × unitInterval) :
    identified point point' ↔
      unitInterval.endpointSetoid point.1 point'.1 ∧
        unitInterval.endpointSetoid point.2 point'.2 := by
  -- Equality in the product torus is exactly coordinatewise kernel equality.
  change
    ((point.1 : UnitAddCircle), (point.2 : UnitAddCircle)) =
        ((point'.1 : UnitAddCircle), (point'.2 : UnitAddCircle)) ↔
      (point.1 : UnitAddCircle) = (point'.1 : UnitAddCircle) ∧
        (point.2 : UnitAddCircle) = (point'.2 : UnitAddCircle)
  constructor
  · intro hpoint
    exact ⟨congrArg Prod.fst hpoint, congrArg Prod.snd hpoint⟩
  · intro hpoint
    exact Prod.ext hpoint.1 hpoint.2

/-- The canonical map from the unit square onto the torus is a quotient map. -/
theorem toTorus_isQuotientMap : Topology.IsQuotientMap toTorus := by
  -- Each coordinate is the continuous, surjective interval-to-circle map.
  have hcontinuous : Continuous (fun x : unitInterval ↦ (x : UnitAddCircle)) :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  have hsurjective : Function.Surjective (fun x : unitInterval ↦ (x : UnitAddCircle)) := by
    intro z
    obtain ⟨b, hb, hbz⟩ := AddCircle.eq_coe_Ico z
    have hb_unit : b ∈ Set.Icc (0 : ℝ) 1 := ⟨hb.1, hb.2.le⟩
    exact ⟨⟨b, hb_unit⟩, hbz⟩
  have hcontinuous_prod :
      Continuous (Prod.map (fun x : unitInterval ↦ (x : UnitAddCircle))
        (fun x : unitInterval ↦ (x : UnitAddCircle))) :=
    hcontinuous.prodMap hcontinuous
  have hsurjective_prod :
      Function.Surjective (Prod.map (fun x : unitInterval ↦ (x : UnitAddCircle))
        (fun x : unitInterval ↦ (x : UnitAddCircle))) :=
    hsurjective.prodMap hsurjective
  -- Compactness of the square and Hausdorffness of the torus close the quotient criterion.
  apply Topology.IsQuotientMap.of_surjective_continuous
  · change Function.Surjective
      (Prod.map (fun x : unitInterval ↦ (x : UnitAddCircle))
        (fun x : unitInterval ↦ (x : UnitAddCircle)))
    exact hsurjective_prod
  · change Continuous
      (Prod.map (fun x : unitInterval ↦ (x : UnitAddCircle))
        (fun x : unitInterval ↦ (x : UnitAddCircle)))
    exact hcontinuous_prod

end TorusSquare


end
