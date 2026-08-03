module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Path

noncomputable section

public section

open Set unitInterval

namespace Circle

/-- The standard quotient parametrization of the circle by the unit interval. -/
def intervalQuotient : C(unitInterval, Circle) :=
  ⟨fun t ↦ AddCircle.homeomorphCircle one_ne_zero (t : UnitAddCircle),
    (AddCircle.homeomorphCircle one_ne_zero).continuous.comp
      ((AddCircle.continuous_mk' 1).comp continuous_subtype_val)⟩

/-- The standard interval parametrization is a quotient map onto the circle. -/
theorem intervalQuotient_isQuotientMap :
    Topology.IsQuotientMap intervalQuotient := by
  -- Every circle point has a representative in the half-open unit interval.
  apply Topology.IsQuotientMap.of_surjective_continuous
  · intro z
    obtain ⟨r, hr, hr_eq⟩ :=
      AddCircle.eq_coe_Ico ((AddCircle.homeomorphCircle one_ne_zero).symm z)
    let t : unitInterval := ⟨r, hr.1, hr.2.le⟩
    refine ⟨t, ?_⟩
    calc
      intervalQuotient t =
          AddCircle.homeomorphCircle one_ne_zero (r : UnitAddCircle) := rfl
      _ = AddCircle.homeomorphCircle one_ne_zero
          ((AddCircle.homeomorphCircle one_ne_zero).symm z) :=
        congrArg (AddCircle.homeomorphCircle one_ne_zero) hr_eq
      _ = z := (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply z
  · exact intervalQuotient.continuous

end Circle

namespace Path

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Helper for Exercise 66.1: the half-open lift of a loop extension recovers the
loop after the standard interval parametrization. -/
private theorem liftIcoExtend_intervalQuotient_apply (f : Path x x) (t : unitInterval) :
    (AddCircle.liftIco 1 0 f.extend ∘
      (AddCircle.homeomorphCircle one_ne_zero).symm) (Circle.intervalQuotient t) = f t := by
  by_cases ht : (t : ℝ) = 1
  · have t_eq : t = (1 : unitInterval) := Subtype.ext ht
    rw [t_eq]
    simp only [Circle.intervalQuotient, ContinuousMap.coe_mk, Function.comp_apply,
      Homeomorph.symm_apply_apply]
    have one_eq_zero : ((1 : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := by
      simpa only [zero_add] using AddCircle.coe_add_period (1 : ℝ) 0
    have intervalOne_eq_zero :
        ((((1 : unitInterval) : ℝ) : UnitAddCircle)) = ((0 : ℝ) : UnitAddCircle) :=
      one_eq_zero
    have zero_mem : (0 : ℝ) ∈ Ico 0 1 := ⟨le_rfl, zero_lt_one⟩
    rw [intervalOne_eq_zero, AddCircle.liftIco_zero_coe_apply zero_mem]
    simp
  · have ht_mem : (t : ℝ) ∈ Ico 0 1 := ⟨t.2.1, lt_of_le_of_ne t.2.2 ht⟩
    simp only [Circle.intervalQuotient, ContinuousMap.coe_mk, Function.comp_apply,
      Homeomorph.symm_apply_apply]
    rw [AddCircle.liftIco_zero_coe_apply ht_mem]
    exact f.extend_extends' t

/-- A loop is constant on the fibers of the standard interval quotient map. -/
theorem factorsThroughIntervalQuotient (f : Path x x) :
    Function.FactorsThrough f.toContinuousMap Circle.intervalQuotient := by
  -- Compare points through the explicit half-open lift of the loop extension.
  intro s t hst
  calc
    f s = (AddCircle.liftIco 1 0 f.extend ∘
        (AddCircle.homeomorphCircle one_ne_zero).symm) (Circle.intervalQuotient s) :=
      (liftIcoExtend_intervalQuotient_apply f s).symm
    _ = (AddCircle.liftIco 1 0 f.extend ∘
        (AddCircle.homeomorphCircle one_ne_zero).symm) (Circle.intervalQuotient t) :=
      congrArg (AddCircle.liftIco 1 0 f.extend ∘
        (AddCircle.homeomorphCircle one_ne_zero).symm) hst
    _ = f t := liftIcoExtend_intervalQuotient_apply f t

/-- Helper for Exercise 66.1: a loop extension has equal values at the endpoints
of the unit interval. -/
private theorem extend_zero_eq_extend_one (f : Path x x) :
    f.extend 0 = f.extend 1 := by
  simp

/-- The circle map obtained by descending a loop through endpoint identification. -/
def toCircleMap (f : Path x x) : C(Circle, X) :=
  ⟨AddCircle.liftIco 1 0 f.extend ∘
      (AddCircle.homeomorphCircle one_ne_zero).symm,
    (AddCircle.liftIco_zero_continuous (extend_zero_eq_extend_one f)
      f.extend.continuous.continuousOn).comp
      (AddCircle.homeomorphCircle one_ne_zero).continuous_invFun⟩

/-- Descending a loop and then pulling back to the interval recovers the loop. -/
theorem toCircleMap_comp (f : Path x x) :
    f.toCircleMap.comp Circle.intervalQuotient = f.toContinuousMap := by
  -- Evaluate the descended map on the standard interval representatives.
  ext t
  exact liftIcoExtend_intervalQuotient_apply f t

/-- The descended circle map is uniquely determined by its pullback to the interval. -/
theorem toCircleMap_unique (f : Path x x) (h : C(Circle, X))
    (h_comp : h.comp Circle.intervalQuotient = f.toContinuousMap) :
    h = f.toCircleMap := by
  -- Surjectivity of the quotient parametrization reduces equality to the interval.
  ext z
  obtain ⟨t, rfl⟩ := Circle.intervalQuotient_isQuotientMap.surjective z
  calc
    h (Circle.intervalQuotient t) = f t := DFunLike.congr_fun h_comp t
    _ = f.toCircleMap (Circle.intervalQuotient t) :=
      (DFunLike.congr_fun (toCircleMap_comp f) t).symm

end Path
