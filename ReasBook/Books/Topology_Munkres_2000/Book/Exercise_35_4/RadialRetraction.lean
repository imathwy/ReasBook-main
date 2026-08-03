module

public import Topology_Munkres_2000.Book.Definition_35_1.Retraction
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Normalize

public section

namespace EuclideanPlane

/-- The Euclidean plane with the origin removed. -/
def punctured : Set (EuclideanSpace ℝ (Fin 2)) :=
  ({0} : Set (EuclideanSpace ℝ (Fin 2)))ᶜ

/-- Helper for Exercise 62.4: a point belongs to the punctured Euclidean plane
exactly when it is nonzero. -/
lemma mem_punctured_iff (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ punctured ↔ x ≠ 0 := by
  -- Unfold the owner definition and use the canonical singleton-complement criterion.
  simpa only [punctured] using
    (Set.mem_compl_singleton_iff : x ∈ ({0} : Set (EuclideanSpace ℝ (Fin 2)))ᶜ ↔ x ≠ 0)

/-- The unit circle, regarded as a subset of the punctured Euclidean plane. -/
def unitCircle : Set punctured :=
  {x | ‖(x : EuclideanSpace ℝ (Fin 2))‖ = 1}

/-- Normalization of a punctured-plane point remains nonzero. -/
theorem normalize_ne_zero (x : punctured) :
    NormedSpace.normalize (x : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
  apply (not_congr (NormedSpace.normalize_eq_zero_iff _)).2
  intro hx
  exact x.property (by simp [hx])

/-- Normalization of a punctured-plane point has unit norm. -/
theorem norm_normalize (x : punctured) :
    ‖NormedSpace.normalize (x : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
  apply NormedSpace.norm_normalize
  intro hx
  exact x.property (by simp [hx])

/-- The radial projection from the punctured plane to its unit circle. -/
noncomputable def radialProjection (x : punctured) : unitCircle :=
  ⟨⟨NormedSpace.normalize (x : EuclideanSpace ℝ (Fin 2)), normalize_ne_zero x⟩,
    norm_normalize x⟩

/-- The radial projection is continuous. -/
theorem continuous_radialProjection : Continuous radialProjection := by
  -- On the punctured plane, normalization is a continuous inverse-norm scalar multiple.
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact ((continuous_norm.comp continuous_subtype_val).inv₀ fun (x : punctured) hx ↦
    x.property (norm_eq_zero.mp hx)).smul continuous_subtype_val

/-- The radial projection fixes every point of the unit circle. -/
theorem radialProjection_leftInverse :
    Function.LeftInverse radialProjection Subtype.val := by
  rintro ⟨⟨x, hx⟩, hnorm⟩
  apply Subtype.ext
  apply Subtype.ext
  exact NormedSpace.normalize_eq_self_of_norm_eq_one hnorm

/-- The radial retraction from the punctured plane onto its unit circle. -/
noncomputable def radialRetraction : Set.Retraction unitCircle where
  toContinuousMap := ⟨radialProjection, continuous_radialProjection⟩
  leftInverse := radialProjection_leftInverse

/-- The ambient value of the radial retraction is vector normalization. -/
theorem radialRetraction_apply (x : punctured) :
    ((radialRetraction.apply x : punctured) : EuclideanSpace ℝ (Fin 2)) =
      NormedSpace.normalize (x : EuclideanSpace ℝ (Fin 2)) := by
  rfl

/-- The unit circle is a retract of the punctured Euclidean plane. -/
theorem unitCircle_isRetract : Set.IsRetract unitCircle :=
  Set.isRetract_iff unitCircle |>.2
    ⟨radialRetraction.toContinuousMap, radialRetraction.leftInverse⟩

end EuclideanPlane
