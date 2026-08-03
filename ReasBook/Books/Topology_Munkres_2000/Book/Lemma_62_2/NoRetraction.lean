module

import all Topology_Munkres_2000.Book.Definition_55_2.Sphere

public import Topology_Munkres_2000.Book.Theorem_55_2
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Topology.MetricSpace.Bounded

public section

open Set

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Helper for Lemma 62.2: radial normalization of a puncture-avoiding map
that fixes the unit sphere gives a retraction of the closed unit disk. -/
lemma punctureAvoidingMapFixedOnUnitSphereIsRetract
    (h : C(Plane, ({0}ᶜ : Set Plane)))
    (hFix : ∀ x, x ∈ Metric.sphere (0 : Plane) 1 → (h x : Plane) = x) :
    Set.IsRetract (StandardSphere.boundary 1) := by
  have hNormalizeContinuous : Continuous (fun x : ClosedUnitBall 1 ↦
      NormedSpace.normalize (h x : Plane)) := by
    unfold NormedSpace.normalize
    have hAmbientContinuous : Continuous (fun x : ClosedUnitBall 1 ↦ (h x : Plane)) :=
      continuous_subtype_val.comp (map_continuous h |>.comp continuous_subtype_val)
    have hNormContinuous : Continuous (fun x : ClosedUnitBall 1 ↦ ‖(h x : Plane)‖) :=
      continuous_norm.comp hAmbientContinuous
    have hNormNe : ∀ x : ClosedUnitBall 1, ‖(h x : Plane)‖ ≠ 0 := by
      intro x hx
      exact (h x).property (norm_eq_zero.mp hx)
    exact (hNormContinuous.inv₀ hNormNe).smul hAmbientContinuous
  have hNormalizeNorm : ∀ x : ClosedUnitBall 1,
      ‖NormedSpace.normalize (h x : Plane)‖ = 1 := by
    intro x
    apply NormedSpace.norm_normalize
    exact (h x).property
  have hNormalizeClosedBall : ∀ x : ClosedUnitBall 1,
      NormedSpace.normalize (h x : Plane) ∈ Metric.closedBall (0 : Plane) 1 := by
    intro x
    rw [Metric.mem_closedBall, dist_zero_right, hNormalizeNorm]
  have hToClosedBallContinuous : Continuous (fun x : ClosedUnitBall 1 ↦
      (⟨NormedSpace.normalize (h x : Plane), hNormalizeClosedBall x⟩ :
        ClosedUnitBall 1)) :=
    hNormalizeContinuous.subtype_mk _
  let r : C(ClosedUnitBall 1, StandardSphere.boundary 1) :=
    ⟨fun x ↦ ⟨⟨NormedSpace.normalize (h x : Plane), hNormalizeClosedBall x⟩,
        hNormalizeNorm x⟩, hToClosedBallContinuous.subtype_mk _⟩
  rw [Set.isRetract_iff]
  refine ⟨r, ?_⟩
  -- On a boundary point, the original map and radial normalization both fix it.
  rintro ⟨x, hxNorm⟩
  rw [StandardSphere.boundary, Set.mem_setOf_eq] at hxNorm
  apply Subtype.ext
  apply Subtype.ext
  have hxSphere : (x : Plane) ∈ Metric.sphere (0 : Plane) 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hxNorm
  simp only [r, ContinuousMap.coe_mk]
  rw [hFix x hxSphere]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one hxNorm

/-- Helper for Lemma 62.2: no map avoiding a point can be the identity outside
a bounded set containing that point. -/
lemma notExistsPunctureAvoidingMapEqOnComplBounded
    (p : Plane) (U : Set Plane) (hU : Bornology.IsBounded U) :
    ¬ ∃ h : C(Plane, ({p}ᶜ : Set Plane)),
      Set.EqOn (fun x ↦ (h x : Plane)) id Uᶜ := by
  rintro ⟨h, hEq⟩
  obtain ⟨R, hRPositive, hUSubset⟩ := hU.subset_ball_lt 0 p
  have hRNe : R ≠ 0 := ne_of_gt hRPositive
  have hNormalizedAvoids : ∀ x : Plane,
      R⁻¹ • ((h (p + R • x) : Plane) - p) ∈ ({0}ᶜ : Set Plane) := by
    intro x
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hx
    have hDifferenceZero : (h (p + R • x) : Plane) - p = 0 := by
      exact (smul_eq_zero.mp hx).resolve_left (inv_ne_zero hRNe)
    exact (h (p + R • x)).property (sub_eq_zero.mp hDifferenceZero)
  have hNormalizedContinuous : Continuous (fun x : Plane ↦
      (⟨R⁻¹ • ((h (p + R • x) : Plane) - p), hNormalizedAvoids x⟩ :
        ({0}ᶜ : Set Plane))) := by
    fun_prop
  let normalized : C(Plane, ({0}ᶜ : Set Plane)) :=
    ⟨fun x ↦ ⟨R⁻¹ • ((h (p + R • x) : Plane) - p), hNormalizedAvoids x⟩,
      hNormalizedContinuous⟩
  have hNormalizedFix : ∀ x, x ∈ Metric.sphere (0 : Plane) 1 →
      (normalized x : Plane) = x := by
    intro x hxSphere
    have hxNorm : ‖x‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hxSphere
    have hAffineOutside : p + R • x ∈ Uᶜ := by
      rw [Set.mem_compl_iff]
      intro hxU
      have hxBall := hUSubset hxU
      rw [Metric.mem_ball, dist_eq_norm] at hxBall
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hRPositive, hxNorm, mul_one] at hxBall
      exact (lt_irrefl R) hxBall
    have hIdentity : (h (p + R • x) : Plane) = p + R • x := hEq hAffineOutside
    simp only [normalized, ContinuousMap.coe_mk]
    rw [hIdentity, add_sub_cancel_left, ← mul_smul, inv_mul_cancel₀ hRNe, one_smul]
  exact unitCircle_not_isRetract_closedUnitDisk
    (punctureAvoidingMapFixedOnUnitSphereIsRetract normalized hNormalizedFix)
