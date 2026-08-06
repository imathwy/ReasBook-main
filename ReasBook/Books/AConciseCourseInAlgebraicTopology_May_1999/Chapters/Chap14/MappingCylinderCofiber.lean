import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Construction_6_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.CollapseSubsetPair

noncomputable section

universe u

/-- The image of `A` inside the mapping-cylinder factorization of the inclusion `A ↪ X`; collapsing
this subspace realizes the standard cofiber replacement of `A ↪ X`. -/
abbrev mappingCylinderCofiberSubspace {X : TopCat.{u}} (A : Set X) :
    Set (subsetInclusion A).mappingCylinder :=
  Set.range (mappingCylinderIn (subsetInclusion A))

/-- The mapping-cylinder projection `M_(A ↪ X) ⟶ X` sends the distinguished cofiber subspace back
into `A`. -/
theorem mappingCylinderProjection_mapsCofiberSubspace
    {X : TopCat.{u}} (A : Set X) :
    ∀ ⦃z : (subsetInclusion A).mappingCylinder⦄,
      z ∈ mappingCylinderCofiberSubspace A →
        mappingCylinderProjection (subsetInclusion A) z ∈ A := by
  intro z hz
  rcases hz with ⟨a, rfl⟩
  have h :
      mappingCylinderProjection (subsetInclusion A) (mappingCylinderIn (subsetInclusion A) a) =
        subsetInclusion A a := by
    simpa using congrArg (fun f ↦ f a) (mappingCylinderFactorization (subsetInclusion A))
  rw [h]
  exact a.2
