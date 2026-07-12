import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import StacksProject_2024.Chap29.Definition_29_57_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

-- Semantic recall: local Section 29.57 precedent already fixes the owner
-- `Scheme.Hom.universallyBoundedFibres`, so this source-facing lemma should live directly on that
-- canonical predicate rather than reintroducing duplicate local fibre-bound definitions.

variable {X Y : Scheme.{u}}

private theorem isClosed_range_fiberToSpecResidueField_of_isImmersion
    (f : X ⟶ Y) [IsImmersion f] (y : Y) :
    IsClosed (Set.range (f.fiberToSpecResidueField y)) := by
  classical
  by_cases h : Nonempty (f.fiber y)
  · let x : f.fiber y := Classical.choice h
    have hsurj : Function.Surjective (f.fiberToSpecResidueField y) := by
      intro z
      exact ⟨x, Subsingleton.elim _ _⟩
    simpa [Set.range_eq_univ.mpr hsurj] using isClosed_univ
  · have hrange : Set.range (f.fiberToSpecResidueField y) = ∅ := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact (h ⟨x⟩).elim
      · intro hz
        cases hz
    simpa [hrange] using isClosed_empty

private theorem fiberToSpecResidueField_isClosedImmersion_of_isImmersion
    (f : X ⟶ Y) [IsImmersion f] (y : Y) :
    IsClosedImmersion (f.fiberToSpecResidueField y) := by
  letI : IsPreimmersion (f.fiberToSpecResidueField y) := by
    simpa [Scheme.Hom.fiberToSpecResidueField] using
      (inferInstance : IsPreimmersion (Limits.pullback.snd f (Y.fromSpecResidueField y)))
  exact IsClosedImmersion.of_isPreimmersion _
    (isClosed_range_fiberToSpecResidueField_of_isImmersion f y)

private theorem fiberGlobalSections_surjective_of_isImmersion
    (f : X ⟶ Y) [IsImmersion f] (y : Y) :
    Function.Surjective (algebraMap (Y.residueField y) (fiberGlobalSections f y)) := by
  letI : IsClosedImmersion (f.fiberToSpecResidueField y) :=
    fiberToSpecResidueField_isClosedImmersion_of_isImmersion f y
  obtain ⟨_, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine
    (f.fiberToSpecResidueField y)
  simpa [fiberGlobalSections, fiberGlobalSectionsAlgebra] using
    hsurj.comp (ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (Y.residueField y)).inv)).2

private theorem fiberDegree_le_one_of_isImmersion
    (f : X ⟶ Y) [IsImmersion f] (y : Y) :
    f.fiberDegree y ≤ 1 := by
  have hsurj :
      Function.Surjective (algebraMap (Y.residueField y) (fiberGlobalSections f y)) :=
    fiberGlobalSections_surjective_of_isImmersion f y
  let φ : (Y.residueField y) →ₐ[(Y.residueField y)] fiberGlobalSections f y :=
    { toRingHom := algebraMap (Y.residueField y) (fiberGlobalSections f y)
      commutes' := fun _ ↦ rfl }
  calc
    Module.finrank (Y.residueField y) (fiberGlobalSections f y)
        = Module.finrank (Y.residueField y)
            ((Y.residueField y) ⧸ RingHom.ker φ.toRingHom) := by
          symm
          exact
            LinearEquiv.finrank_eq
              (Ideal.quotientKerAlgEquivOfSurjective hsurj).toLinearEquiv
    _ ≤ Module.finrank (Y.residueField y) (Y.residueField y) := by
      simpa [φ] using
        Submodule.finrank_quotient_le (RingHom.ker φ.toRingHom)
    _ = 1 := Module.finrank_self (Y.residueField y)

/-- Lemma 29.57.7: an immersion has fibre degrees bounded by `1`. -/
@[stacks 03J9]
theorem degreesOfFibresBoundedBy_one_of_isImmersion
    (f : X ⟶ Y) [IsImmersion f] :
    degreesOfFibresBoundedBy f 1 := by
  intro y
  have hfinite : IsFinite (f.fiberToSpecResidueField y) := by
    letI : IsClosedImmersion (f.fiberToSpecResidueField y) :=
      fiberToSpecResidueField_isClosedImmersion_of_isImmersion f y
    infer_instance
  exact ⟨hfinite, fiberDegree_le_one_of_isImmersion f y⟩

/-- Lemma 29.57.7: an immersion has universally bounded fibres, with uniform bound `1`. -/
@[stacks 03J9]
theorem universallyBoundedFibres_of_isImmersion
    (f : X ⟶ Y) [IsImmersion f] :
    universallyBoundedFibres f :=
  ⟨1, degreesOfFibresBoundedBy_one_of_isImmersion f⟩

end Scheme.Hom
end AlgebraicGeometry
