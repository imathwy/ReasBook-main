module

public import Topology_Munkres_2000.Book.Example_18_6

public section

open Complex Set

/-- The parametrization `halfOpenUnitIntervalToCircle` viewed as a map into the ambient
complex plane. -/
noncomputable abbrev halfOpenUnitIntervalToPlane : Set.Ico (0 : ℝ) 1 → ℂ :=
  Subtype.val ∘ halfOpenUnitIntervalToCircle

/-- The plane-valued parametrization is the codomain expansion of
`halfOpenUnitIntervalToCircle`. -/
@[simp]
theorem halfOpenUnitIntervalToPlane_apply (t : Set.Ico (0 : ℝ) 1) :
    halfOpenUnitIntervalToPlane t = (halfOpenUnitIntervalToCircle t : ℂ) := rfl

/-- Helper for Example 18.7: the codomain-expanded parametrization is continuous. -/
theorem halfOpenUnitIntervalToPlane_continuous :
    Continuous halfOpenUnitIntervalToPlane :=
  halfOpenUnitIntervalToCircle_continuous.subtype_val

/-- Helper for Example 18.7: the codomain-expanded parametrization is injective. -/
theorem halfOpenUnitIntervalToPlane_injective :
    Function.Injective halfOpenUnitIntervalToPlane := by
  intro s t h
  apply halfOpenUnitIntervalToCircle_bijective.injective
  exact Subtype.ext h

/-- Example 18.7. The codomain-expanded parametrization is not a topological embedding. -/
theorem halfOpenUnitIntervalToPlane_not_isEmbedding :
    ¬ Topology.IsEmbedding halfOpenUnitIntervalToPlane := by
  intro hPlaneEmbedding
  -- Reflect the assumed embedding through the canonical inclusion `Circle → ℂ`.
  have hCircleEmbedding : Topology.IsEmbedding halfOpenUnitIntervalToCircle := by
    exact Topology.IsEmbedding.subtypeVal.of_comp_iff.mp hPlaneEmbedding
  -- Surjectivity then promotes the circle parametrization to a forbidden homeomorphism.
  have hCircleHomeomorph : IsHomeomorph halfOpenUnitIntervalToCircle := by
    exact isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨hCircleEmbedding, halfOpenUnitIntervalToCircle_bijective.surjective⟩
  exact halfOpenUnitIntervalToCircle_not_isHomeomorph hCircleHomeomorph
