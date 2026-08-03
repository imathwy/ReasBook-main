module

public import Topology_Munkres_2000.Book.Exercise_35_4.RadialRetraction
public import Mathlib.Topology.Homotopy.Contractible

import all Topology_Munkres_2000.Book.Exercise_35_4.RadialRetraction
import Topology_Munkres_2000.Book.Lemma_55_1
import Topology_Munkres_2000.Book.Lemma_55_3
import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup

public section

namespace EuclideanPlane

/-- The canonical inclusion of the unit circle into the punctured Euclidean plane. -/
@[expose]
def unitCircleInclusion : C(unitCircle, punctured) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The unit-circle inclusion acts by the underlying subtype coercion. -/
@[simp]
theorem unitCircleInclusion_apply (x : unitCircle) :
    unitCircleInclusion x = x := rfl

/-- Helper for Corollary 55.4: forgetting the punctured-plane subtype identifies
the nested unit circle with the Euclidean unit sphere. -/
private lemma subtypeVal_image_unitCircle :
    (Subtype.val : punctured → EuclideanSpace ℝ (Fin 2)) '' unitCircle =
      Metric.sphere 0 1 := by
  -- Reduce both sets to the unit-norm condition, constructing the punctured point backwards.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [unitCircle, Set.mem_setOf_eq, Metric.mem_sphere,
      dist_zero_right] using hy
  · intro hx
    have hxnorm : ‖x‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hx
    have hxne : x ≠ 0 := by
      intro hxzero
      rw [hxzero, norm_zero] at hxnorm
      exact zero_ne_one hxnorm
    have hxpunctured : x ∈ punctured := (mem_punctured_iff x).mpr hxne
    let y : punctured := ⟨x, hxpunctured⟩
    refine ⟨y, ?_, ?_⟩
    · exact hxnorm
    · rfl

/-- Helper for Corollary 55.4: the standard real-linear isometry gives complex
coordinates on the Euclidean plane. -/
private noncomputable def planeComplexIsometry :
    EuclideanSpace ℝ (Fin 2) ≃ᵢ ℂ :=
  -- Use the coordinates associated to the standard orthonormal basis `(1, I)`.
  Complex.orthonormalBasisOneI.repr.symm

/-- Helper for Corollary 55.4: standard complex coordinates carry the Euclidean
unit sphere onto `Circle`. -/
private lemma planeComplexIsometry_image_unitSphere :
    planeComplexIsometry ''
        (Metric.sphere 0 1 : Set (EuclideanSpace ℝ (Fin 2))) =
      (Submonoid.unitSphere ℂ : Set ℂ) := by
  -- Isometries preserve spheres, and this linear isometry sends zero to zero.
  rw [planeComplexIsometry.image_sphere]
  simp [Submonoid.unitSphere, planeComplexIsometry]

/-- Helper for Corollary 55.4: the nested Euclidean unit circle is
homeomorphic to the canonical complex circle. -/
private noncomputable def unitCircleHomeomorphCircle : unitCircle ≃ₜ Circle :=
  -- Normalize the nested subtype to a sphere, then transport that sphere to `Circle`.
  (Topology.IsEmbedding.subtypeVal.homeomorphImage unitCircle).trans
    ((Homeomorph.setCongr subtypeVal_image_unitCircle).trans
      ((planeComplexIsometry.toHomeomorph.isEmbedding.homeomorphImage
        (Metric.sphere 0 1)).trans
          (Homeomorph.setCongr planeComplexIsometry_image_unitSphere)))

/-- Helper for Corollary 55.4: the Euclidean unit circle is not contractible. -/
private lemma unitCircle_not_contractible : ¬ ContractibleSpace unitCircle := by
  -- Transport a hypothetical contraction to `Circle`, whose fundamental group is nontrivial.
  intro hcontractible
  letI : ContractibleSpace unitCircle := hcontractible
  letI : ContractibleSpace Circle := unitCircleHomeomorphCircle.symm.contractibleSpace
  have hsub : Subsingleton (FundamentalGroup Circle 1) := inferInstance
  have hsubInt : Subsingleton (Multiplicative ℤ) :=
    Circle.fundamentalGroupEquivInt.toEquiv.subsingleton_congr.mp hsub
  exact not_subsingleton_iff_nontrivial.mpr inferInstance hsubInt

/-- Helper for Corollary 55.4: radial retraction after unit-circle inclusion is
the identity map. -/
private lemma radialRetraction_comp_unitCircleInclusion :
    radialRetraction.toContinuousMap.comp unitCircleInclusion =
      ContinuousMap.id unitCircle := by
  -- Evaluate the composite and apply the defining left-inverse law of the retraction.
  apply ContinuousMap.ext
  intro x
  simpa only [ContinuousMap.comp_apply, unitCircleInclusion_apply,
    ContinuousMap.id_apply] using radialRetraction.leftInverse x

end EuclideanPlane

open EuclideanPlane

/-- Corollary 55.4 (1). The inclusion of the unit circle into the punctured
Euclidean plane is not nullhomotopic. -/
theorem EuclideanPlane.unitCircleInclusion_not_nullhomotopic :
    ¬ unitCircleInclusion.Nullhomotopic := by
  -- Postcompose a hypothetical nullhomotopy with the radial retraction to contract the identity.
  intro hinclusion
  have hid : (ContinuousMap.id unitCircle).Nullhomotopic := by
    rw [← radialRetraction_comp_unitCircleInclusion]
    exact hinclusion.comp_right radialRetraction.toContinuousMap
  have hcontractible : ContractibleSpace unitCircle :=
    (contractible_iff_id_nullhomotopic unitCircle).mpr hid
  exact unitCircle_not_contractible hcontractible

/-- Corollary 55.4 (2). The identity map of the unit circle is not
nullhomotopic. -/
theorem EuclideanPlane.unitCircle_id_not_nullhomotopic :
    ¬ (ContinuousMap.id unitCircle).Nullhomotopic := by
  -- Postcompose a hypothetical identity nullhomotopy with the inclusion and use the first part.
  intro hid
  have hinclusion : unitCircleInclusion.Nullhomotopic := by
    simpa only [ContinuousMap.comp_id] using hid.comp_right unitCircleInclusion
  exact unitCircleInclusion_not_nullhomotopic hinclusion
