module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Analysis.Real.Sqrt

public section

open Set

namespace ParabolaFiber

/-- The value `x + y ^ 2` determining the parabola fiber of a point. -/
def value (p : ℝ × ℝ) : ℝ := p.1 + p.2 ^ 2

/-- The parabola fiber value function is continuous. -/
theorem continuous_value : Continuous value := by
  unfold value
  fun_prop

/-- The continuous map whose fibers define the parabola equivalence relation. -/
def map : C(ℝ × ℝ, ℝ) := ⟨value, continuous_value⟩

/-- A continuous section of the parabola fiber value map. -/
def sectionMap : C(ℝ, ℝ × ℝ) := ⟨fun t ↦ (t, 0), continuous_id.prodMk continuous_const⟩

/-- `sectionMap` is a right inverse of the parabola fiber value map. -/
theorem sectionMap_rightInverse : Function.RightInverse sectionMap map := by
  intro t
  simp [map, sectionMap, value]

/-- The equivalence relation whose classes are the fibers of `(x, y) ↦ x + y ^ 2`. -/
def setoid : Setoid (ℝ × ℝ) := Setoid.ker map

/-- Two points are in the same parabola fiber exactly when their values of `x + y ^ 2` agree. -/
@[simp]
theorem rel_iff (p q : ℝ × ℝ) :
    setoid p q ↔ p.1 + p.2 ^ 2 = q.1 + q.2 ^ 2 := by
  rfl

/-- The parabola fiber value map is a quotient map. -/
theorem isQuotientMap : Topology.IsQuotientMap map :=
  Topology.IsQuotientMap.of_inverse sectionMap.continuous map.continuous sectionMap_rightInverse

/-- Exercise 22.4 (1): the quotient of `ℝ × ℝ` by equality of `x + y ^ 2` is
homeomorphic to `ℝ`. -/
def quotientHomeomorph : Quotient setoid ≃ₜ ℝ :=
  sectionMap_rightInverse.homeomorph

/-- The parabola fiber quotient homeomorphism evaluates a class by `x + y ^ 2`. -/
@[simp]
theorem quotientHomeomorph_mk (p : ℝ × ℝ) :
    quotientHomeomorph (Quotient.mk setoid p) = map p := by
  rfl

end ParabolaFiber

namespace RadiusSquaredFiber

/-- The squared radius `x ^ 2 + y ^ 2` of a point. -/
def value (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2

/-- The squared radius is nonnegative. -/
theorem value_nonneg (p : ℝ × ℝ) : 0 ≤ value p := by
  exact add_nonneg (sq_nonneg p.1) (sq_nonneg p.2)

/-- The squared radius as a map to the nonnegative ray `Ici 0`. -/
def mapValue (p : ℝ × ℝ) : Ici (0 : ℝ) := ⟨value p, value_nonneg p⟩

/-- The squared-radius map to `Ici 0` is continuous. -/
theorem continuous_mapValue : Continuous mapValue := by
  exact (continuous_fst.pow 2 |>.add <| continuous_snd.pow 2).subtype_mk value_nonneg

/-- The continuous squared-radius map to the nonnegative ray. -/
def map : C(ℝ × ℝ, Ici (0 : ℝ)) := ⟨mapValue, continuous_mapValue⟩

/-- A continuous section of the squared-radius map. -/
noncomputable def sectionMap : C(Ici (0 : ℝ), ℝ × ℝ) :=
  ⟨fun t ↦ (√t, 0),
    (Real.continuous_sqrt.comp continuous_subtype_val).prodMk continuous_const⟩

/-- `sectionMap` is a right inverse of the squared-radius map. -/
theorem sectionMap_rightInverse : Function.RightInverse sectionMap map := by
  intro t
  ext
  simp [map, mapValue, sectionMap, value]

/-- The equivalence relation whose classes are the fibers of `(x, y) ↦ x ^ 2 + y ^ 2`. -/
def setoid : Setoid (ℝ × ℝ) := Setoid.ker map

/-- Two points have the same squared-radius fiber exactly when their squared radii agree. -/
@[simp]
theorem rel_iff (p q : ℝ × ℝ) :
    setoid p q ↔ p.1 ^ 2 + p.2 ^ 2 = q.1 ^ 2 + q.2 ^ 2 := by
  change map p = map q ↔ _
  constructor
  · exact fun h ↦ congrArg Subtype.val h
  · exact fun h ↦ Subtype.ext h

/-- The squared-radius map to `Ici 0` is a quotient map. -/
theorem isQuotientMap : Topology.IsQuotientMap map :=
  Topology.IsQuotientMap.of_inverse sectionMap.continuous map.continuous sectionMap_rightInverse

/-- Exercise 22.4 (2): the quotient of `ℝ × ℝ` by equality of
`x ^ 2 + y ^ 2` is homeomorphic to the nonnegative ray `Ici 0`. -/
noncomputable def quotientHomeomorph : Quotient setoid ≃ₜ Ici (0 : ℝ) :=
  sectionMap_rightInverse.homeomorph

/-- The squared-radius quotient homeomorphism evaluates a class by its squared radius. -/
@[simp]
theorem quotientHomeomorph_mk (p : ℝ × ℝ) :
    quotientHomeomorph (Quotient.mk setoid p) = map p := by
  rfl

end RadiusSquaredFiber
