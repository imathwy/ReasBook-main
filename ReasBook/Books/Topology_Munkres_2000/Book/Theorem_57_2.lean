module

public import Topology_Munkres_2000.Book.Definition_57_2.Antipodal

import Topology_Munkres_2000.Book.Exercise_55_5.Inclusion
import Topology_Munkres_2000.Book.Theorem_57_1
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section

public section

/-- Helper for Theorem 57.2: adjoining a leading real coordinate to a Euclidean
vector through the canonical coordinate equivalence. -/
private def prependCoordinate {n : ℕ} (c : ℝ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm
    (Fin.cons c (EuclideanSpace.equiv (Fin (n + 1)) ℝ v))

/-- Helper for Theorem 57.2: adjoining a leading coordinate adds its square to
the squared Euclidean norm. -/
private theorem prependCoordinate_norm_sq {n : ℕ} (c : ℝ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖prependCoordinate c v‖ ^ 2 = c ^ 2 + ‖v‖ ^ 2 := by
  -- Ordinary coordinates reduce the norm identity to splitting a finite sum.
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ]
  simp [prependCoordinate]

/-- Helper for Theorem 57.2: adjoining a leading coordinate commutes with
negation. -/
private theorem prependCoordinate_neg {n : ℕ} (c : ℝ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    prependCoordinate (-c) (-v) = -prependCoordinate c v := by
  -- Compare coordinates, where `Fin.cons` commutes pointwise with negation.
  apply (EuclideanSpace.equiv (Fin (n + 2)) ℝ).injective
  simp only [prependCoordinate, ContinuousLinearEquiv.apply_symm_apply, map_neg]
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

/-- Helper for Theorem 57.2: adjoining a varying leading coordinate to a
varying Euclidean vector is continuous. -/
private theorem continuous_prependCoordinate {n : ℕ} :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin (n + 1)) ↦
      prependCoordinate p.1 p.2) := by
  -- Check continuity through the coordinate equivalence, one coordinate at a time.
  apply (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact continuous_fst
  · exact (continuous_apply j).comp
      ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).continuous.comp continuous_snd)

namespace StandardSphere

/-- Helper for Theorem 57.2: the square-root radicand defining the upper
hemisphere is nonnegative on the closed unit ball. -/
private theorem upperHemisphere_radicand_nonneg {n : ℕ} (y : ClosedUnitBall n) :
    0 ≤ 1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 := by
  -- Closed-ball membership bounds the norm by one and hence controls its square.
  have hy_norm : ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := by
    simpa [Real.norm_eq_abs] using Metric.mem_closedBall.mp y.property
  nlinarith [norm_nonneg (y : EuclideanSpace ℝ (Fin (n + 1)))]

/-- Helper for Theorem 57.2: the upper-hemisphere coordinate formula has unit
norm. -/
private theorem upperHemispherePoint_mem_sphere {n : ℕ} (y : ClosedUnitBall n) :
    prependCoordinate
        (Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) y ∈
      StandardSphere (n + 1) := by
  -- The leading coordinate supplies exactly the squared norm missing from `y`.
  rw [mem_sphere_zero_iff_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [prependCoordinate_norm_sq, Real.sq_sqrt (upperHemisphere_radicand_nonneg y)]
  ring

/-- Helper for Theorem 57.2: the coordinate formula for the upper hemisphere
is continuous. -/
private theorem continuous_upperHemispherePoint (n : ℕ) :
    Continuous (fun y : ClosedUnitBall n ↦
      (⟨prependCoordinate
          (Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) y,
        upperHemispherePoint_mem_sphere y⟩ : StandardSphere (n + 1))) := by
  -- Separate continuity of the height from continuity of the ball projection.
  have height_continuous : Continuous (fun y : ClosedUnitBall n ↦
      Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) := by
    fun_prop
  have vector_continuous : Continuous (fun y : ClosedUnitBall n ↦
      (y : EuclideanSpace ℝ (Fin (n + 1)))) := continuous_subtype_val
  exact Continuous.subtype_mk
    (continuous_prependCoordinate.comp (height_continuous.prodMk vector_continuous)) _

/-- Helper for Theorem 57.2: the closed unit ball parametrizes the upper
hemisphere of the next-dimensional standard sphere. -/
private def upperHemisphere (n : ℕ) : C(ClosedUnitBall n, StandardSphere (n + 1)) :=
  ⟨fun y ↦ ⟨prependCoordinate
      (Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) y,
    upperHemispherePoint_mem_sphere y⟩, continuous_upperHemispherePoint n⟩

/-- Helper for Theorem 57.2: the standard equator is the boundary restriction
of the upper-hemisphere parametrization. -/
private def equator (n : ℕ) : C(StandardSphere n, StandardSphere (n + 1)) :=
  (upperHemisphere n).comp (toBall n)

/-- Helper for Theorem 57.2: the equator has zero leading coordinate and keeps
the original sphere point in its remaining coordinates. -/
private theorem equator_coe (n : ℕ) (x : StandardSphere n) :
    (equator n x : EuclideanSpace ℝ (Fin (n + 2))) = prependCoordinate 0 x := by
  -- On the boundary the norm is one, so the upper-hemisphere height vanishes.
  rw [equator, ContinuousMap.comp_apply]
  simp only [upperHemisphere, ContinuousMap.coe_mk, toBall_apply]
  congr 1
  rw [mem_sphere_zero_iff_norm.mp x.property, one_pow, sub_self, Real.sqrt_zero]

/-- Helper for Theorem 57.2: the standard equator preserves antipodes. -/
private theorem equator_odd (n : ℕ) : Function.Odd (equator n) := by
  -- The stable ambient-coordinate formula makes compatibility with negation explicit.
  intro x
  apply Subtype.ext
  calc
    (equator n (-x) : EuclideanSpace ℝ (Fin (n + 2))) = prependCoordinate 0 (-x) :=
      equator_coe n (-x)
    _ = prependCoordinate 0 (-(x : EuclideanSpace ℝ (Fin (n + 1)))) := by
      congr 1
    _ = -prependCoordinate 0 x := by
      rw [← prependCoordinate_neg, neg_zero]
    _ = -(equator n x : EuclideanSpace ℝ (Fin (n + 2))) :=
      congrArg Neg.neg (equator_coe n x).symm
    _ = ((-(equator n x) : StandardSphere (n + 1)) :
        EuclideanSpace ℝ (Fin (n + 2))) := rfl

/-- Helper for Theorem 57.2: the standard equator is nullhomotopic because it
extends across the contractible closed unit ball. -/
private theorem equator_nullhomotopic (n : ℕ) : (equator n).Nullhomotopic := by
  -- Restrict the nullhomotopic ball identity and postcompose by the extension.
  have unit_radius_nonnegative : (0 : ℝ) ≤ 1 := by
    positivity
  letI : ContractibleSpace (ClosedUnitBall n) :=
    Metric.contractibleSpace_closedBall unit_radius_nonnegative
  have inclusion_null : (toBall n).Nullhomotopic :=
    (id_nullhomotopic (ClosedUnitBall n)).comp_left (toBall n)
  exact inclusion_null.comp_right (upperHemisphere n)

end StandardSphere

/-- Theorem 57.2. There is no continuous antipode-preserving map from `S²` to `S¹`. -/
theorem notExistsOddMapSphereTwoToOne :
    ¬ ∃ g : C(StandardSphere 2, StandardSphere 1), Function.Odd g := by
  -- Restrict a hypothetical odd map to the odd equator of `S²`.
  rintro ⟨g, g_odd⟩
  let h : C(StandardSphere 1, StandardSphere 1) :=
    g.comp (StandardSphere.equator 1)
  have h_odd : Function.Odd h :=
    g_odd.comp_odd (StandardSphere.equator_odd 1)
  -- The equator extends over a contractible ball, so the restriction is nullhomotopic.
  have h_null : h.Nullhomotopic :=
    (StandardSphere.equator_nullhomotopic 1).comp_right g
  exact oddCircleMap_not_nullhomotopic h h_odd h_null
