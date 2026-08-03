module

public import Topology_Munkres_2000.Book.Example_22_5.Torus
public import Topology_Munkres_2000.Book.Example_74_8.StandardGluing
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

public section

namespace ProjectivePlaneTorus

noncomputable section

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Helper for Example 74.8: standard complex coordinates identify the Euclidean plane
with the complex plane. -/
private noncomputable def planeHomeomorphComplex : Plane ≃ₜ ℂ :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph

/-- Helper for Example 74.8: standard complex coordinates preserve the unit-sphere
predicate. -/
private lemma planeHomeomorphComplex_mem_unitSphere (point : Plane) :
    point ∈ Metric.sphere (0 : Plane) 1 ↔
      planeHomeomorphComplex point ∈ Metric.sphere (0 : ℂ) 1 := by
  -- The coordinate equivalence is a linear isometry, so it preserves norms.
  simp only [Metric.mem_sphere, dist_zero_right]
  exact (Complex.orthonormalBasisOneI.repr.symm.norm_map point).symm ▸ Iff.rfl

/-- Helper for Example 74.8: standard complex coordinates identify the Euclidean unit
circle with `Circle`. -/
private noncomputable def unitSphereHomeomorphCircle :
    Metric.sphere (0 : Plane) 1 ≃ₜ Circle :=
  planeHomeomorphComplex.subtype planeHomeomorphComplex_mem_unitSphere

/-- Helper for Example 74.8: the boundary-radius scaling factor is nonzero. -/
private lemma half_ne_zero : (1 / 2 : ℝ) ≠ 0 := by
  norm_num

/-- Helper for Example 74.8: multiplication by one half carries the unit Euclidean circle
onto the boundary circle used by the deleted-disc gluing. -/
private lemma halfScale_mem_boundaryCircle (point : Plane) :
    point ∈ Metric.sphere (0 : Plane) 1 ↔
      (Homeomorph.smulOfNeZero (1 / 2 : ℝ) half_ne_zero point) ∈
        DiscBoundaryGluing.BoundaryCircle := by
  -- Scaling multiplies the norm by `1 / 2`, hence changes radius one to radius one half.
  simp only [Metric.mem_sphere, dist_zero_right, Homeomorph.smulOfNeZero_apply,
    norm_smul, Real.norm_eq_abs]
  norm_num

/-- Helper for Example 74.8: the additive unit circle is canonically homeomorphic to the
attaching boundary circle of radius one half. -/
private noncomputable def unitAddCircleHomeomorphBoundaryCircle :
    UnitAddCircle ≃ₜ DiscBoundaryGluing.BoundaryCircle :=
  (AddCircle.homeomorphCircle one_ne_zero).trans
    (unitSphereHomeomorphCircle.symm.trans
      ((Homeomorph.smulOfNeZero (1 / 2 : ℝ) half_ne_zero).subtype
        halfScale_mem_boundaryCircle))

/-- Helper for Example 74.8: coercion of the closed unit interval onto the additive unit
circle is a quotient map. -/
private lemma unitIntervalCoe_isQuotientMap :
    Topology.IsQuotientMap (fun point : unitInterval ↦ (point : UnitAddCircle)) := by
  -- The interval coercion is continuous and every circle class has a representative in
  -- the half-open unit interval, hence in the closed unit interval.
  apply Topology.IsQuotientMap.of_surjective_continuous
  · intro point
    obtain ⟨representative, hrepresentative, rfl⟩ := AddCircle.eq_coe_Ico point
    exact ⟨⟨representative, hrepresentative.1, hrepresentative.2.le⟩, rfl⟩
  · exact (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val

/-- Helper for Example 74.8: the standard interval parametrization of the attaching boundary
circle. -/
noncomputable def boundaryCircleParam :
    unitInterval → DiscBoundaryGluing.BoundaryCircle :=
  fun point ↦ unitAddCircleHomeomorphBoundaryCircle (point : UnitAddCircle)

/-- Helper for Example 74.8: the standard interval parametrization is a quotient map onto the
attaching boundary circle. -/
lemma boundaryCircleParam_isQuotientMap :
    Topology.IsQuotientMap boundaryCircleParam := by
  -- Postcomposing the interval quotient with a homeomorphism preserves quotientness.
  change Topology.IsQuotientMap
    (unitAddCircleHomeomorphBoundaryCircle ∘
      fun point : unitInterval ↦ (point : UnitAddCircle))
  exact unitAddCircleHomeomorphBoundaryCircle.isQuotientMap.comp
    unitIntervalCoe_isQuotientMap

/-- Helper for Example 74.8: equality after coercion to the additive circle is precisely the
exported endpoint-identification relation on the closed interval. -/
private lemma unitIntervalCoe_eq_iff_endpointSetoid (s t : unitInterval) :
    (s : UnitAddCircle) = (t : UnitAddCircle) ↔ unitInterval.endpointSetoid s t := by
  constructor
  · intro hst
    -- Choose the half-open representatives unless one parameter is the endpoint `1`.
    apply (unitInterval.endpointSetoid_iff s t).2
    have hzero_mem : (0 : ℝ) ∈ Set.Ico 0 (0 + 1) := by
      norm_num
    by_cases hs_one : s = 1
    · by_cases ht_one : t = 1
      · exact Or.inl (hs_one.trans ht_one.symm)
      · have ht_lt_one : (t : ℝ) < 1 :=
          lt_of_le_of_ne (unitInterval.le_one t) (unitInterval.coe_ne_one.mpr ht_one)
        have ht_mem : (t : ℝ) ∈ Set.Ico 0 (0 + 1) :=
          ⟨unitInterval.nonneg t, by simpa only [zero_add] using ht_lt_one⟩
        have ht_circle_zero : (t : UnitAddCircle) = 0 := by
          calc
            (t : UnitAddCircle) = (s : UnitAddCircle) := hst.symm
            _ = ((1 : ℝ) : UnitAddCircle) :=
              congrArg (fun z : unitInterval ↦ (z : UnitAddCircle)) hs_one
            _ = 0 := AddCircle.coe_period (1 : ℝ)
        have ht_coe_zero : ((t : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := by
          calc
            ((t : ℝ) : UnitAddCircle) = 0 := ht_circle_zero
            _ = ((0 : ℝ) : UnitAddCircle) := (AddCircle.coe_zero (1 : ℝ)).symm
        have ht_val_zero : (t : ℝ) = 0 :=
          (AddCircle.coe_eq_coe_iff_of_mem_Ico ht_mem hzero_mem).mp ht_coe_zero
        exact Or.inr (Or.inr ⟨hs_one, Subtype.ext ht_val_zero⟩)
    · have hs_lt_one : (s : ℝ) < 1 :=
        lt_of_le_of_ne (unitInterval.le_one s) (unitInterval.coe_ne_one.mpr hs_one)
      have hs_mem : (s : ℝ) ∈ Set.Ico 0 (0 + 1) :=
        ⟨unitInterval.nonneg s, by simpa only [zero_add] using hs_lt_one⟩
      by_cases ht_one : t = 1
      · have hs_circle_zero : (s : UnitAddCircle) = 0 := by
          calc
            (s : UnitAddCircle) = (t : UnitAddCircle) := hst
            _ = ((1 : ℝ) : UnitAddCircle) :=
              congrArg (fun z : unitInterval ↦ (z : UnitAddCircle)) ht_one
            _ = 0 := AddCircle.coe_period (1 : ℝ)
        have hs_coe_zero : ((s : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := by
          calc
            ((s : ℝ) : UnitAddCircle) = 0 := hs_circle_zero
            _ = ((0 : ℝ) : UnitAddCircle) := (AddCircle.coe_zero (1 : ℝ)).symm
        have hs_val_zero : (s : ℝ) = 0 :=
          (AddCircle.coe_eq_coe_iff_of_mem_Ico hs_mem hzero_mem).mp hs_coe_zero
        exact Or.inr (Or.inl ⟨Subtype.ext hs_val_zero, ht_one⟩)
      · have ht_lt_one : (t : ℝ) < 1 :=
          lt_of_le_of_ne (unitInterval.le_one t) (unitInterval.coe_ne_one.mpr ht_one)
        have ht_mem : (t : ℝ) ∈ Set.Ico 0 (0 + 1) :=
          ⟨unitInterval.nonneg t, by simpa only [zero_add] using ht_lt_one⟩
        have hst_val : (s : ℝ) = (t : ℝ) :=
          (AddCircle.coe_eq_coe_iff_of_mem_Ico hs_mem ht_mem).mp hst
        exact Or.inl (Subtype.ext hst_val)
  · intro hst
    -- The only nontrivial relation branches are the two orders of the periodic endpoints.
    rcases (unitInterval.endpointSetoid_iff s t).1 hst with hst | hst | hst
    · exact congrArg (fun z : unitInterval ↦ (z : UnitAddCircle)) hst
    · calc
        (s : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) :=
          congrArg (fun z : unitInterval ↦ (z : UnitAddCircle)) hst.1
        _ = 0 := AddCircle.coe_zero (1 : ℝ)
        _ = ((1 : ℝ) : UnitAddCircle) := (AddCircle.coe_period (1 : ℝ)).symm
        _ = (t : UnitAddCircle) :=
          (congrArg (fun z : unitInterval ↦ (z : UnitAddCircle)) hst.2).symm
    · calc
        (s : UnitAddCircle) = ((1 : ℝ) : UnitAddCircle) :=
          congrArg (fun z : unitInterval ↦ (z : UnitAddCircle)) hst.1
        _ = 0 := AddCircle.coe_period (1 : ℝ)
        _ = ((0 : ℝ) : UnitAddCircle) := (AddCircle.coe_zero (1 : ℝ)).symm
        _ = (t : UnitAddCircle) :=
          (congrArg (fun z : unitInterval ↦ (z : UnitAddCircle)) hst.2).symm

/-- Helper for Example 74.8: two interval parameters determine the same attaching-boundary
point exactly when they are equal modulo endpoint identification. -/
lemma boundaryCircleParam_eq_iff (s t : unitInterval) :
    boundaryCircleParam s = boundaryCircleParam t ↔ unitInterval.endpointSetoid s t := by
  -- Injectivity of the circle homeomorphism reduces the kernel to the defining interval kernel.
  rw [boundaryCircleParam, boundaryCircleParam,
    unitAddCircleHomeomorphBoundaryCircle.injective.eq_iff]
  exact unitIntervalCoe_eq_iff_endpointSetoid s t

end

end ProjectivePlaneTorus
