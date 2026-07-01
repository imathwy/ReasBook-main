import stacks_project.Chap04.Lemma_4_35_3
import stacks_project.Chap08.Definition_8_5_1
import stacks_project.Chap08.Lemma_8_5_3.PreimageWitness

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-- Helper for Lemma 8.5.3: the imported PreimageWitness theorem gives the required coverwise
descent equivalence for the associated groupoid projection on each fixed cover. -/
private theorem strongly_cartesian_projection_coverwise_descent_equivalence
    [IsStackOnSite J p] {U : C} (cover : J.Cover U) :
    ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).toDescentData
      (fun I : cover.Arrow ↦ I.f)).IsEquivalence := by
  -- The fixed-cover source step is delegated to the canonical helper owner imported above.
  exact associated_groupoid_cover_toDescentData_isEquivalence (J := J) (p := p) cover

/-- Helper for Lemma 8.5.3: once the fixed-cover associated descent functors are equivalences for
every cover, the standard coverwise criterion upgrades the associated projection to a stack on the
site. -/
theorem stronglyCartesianProjection_isStackOnSite
    [IsStackOnSite J p] :
    IsStackOnSite J (stronglyCartesianProjection p) := by
  letI : IsFibredInGroupoids (stronglyCartesianProjection p) :=
    stronglyCartesianProjection_isFibredInGroupoids p
  -- Route correction: the fixed-cover comparison package now lives in `PreimageWitness`, so this
  -- file only applies the standard coverwise stack criterion to that imported theorem.
  refine
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      J (stronglyCartesianProjection p)).2 ?_
  intro U cover
  -- Reuse the dedicated fixed-cover helper so the wrapper theorem only runs the coverwise
  -- criterion from the source proof.
  exact strongly_cartesian_projection_coverwise_descent_equivalence
    (J := J) (p := p) cover

/-- Lemma 8.5.3: if `p : S ⥤ C` is a stack over the site `(C, J)`, then the associated category
fibred in groupoids `stronglyCartesianProjection p` is a stack in groupoids over `(C, J)`. -/
theorem associatedGroupoidProjection_isStack
    [IsStackOnSite J p] :
    IsStackInGroupoids J (stronglyCartesianProjection p) := by
  -- The final step only packages the site-level stack statement with the Chapter 4
  -- fibred-in-groupoids structure on the associated strongly-cartesian projection.
  exact
    { toIsStackOnSite :=
        stronglyCartesianProjection_isStackOnSite (J := J) (p := p)
      toIsFibredInGroupoids :=
        stronglyCartesianProjection_isFibredInGroupoids p }

end

end CategoryTheory
