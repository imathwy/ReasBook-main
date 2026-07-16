import StacksProject_2024.stacks_project.Chap17.Lemma_17_10_4

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

theorem fiber_isLocallyNoetherian_of_locallyOfFiniteType_probe [LocallyOfFiniteType f] (s : S) :
    IsLocallyNoetherian (Scheme.Hom.fiber f s) := by
  let _ : LocallyOfFiniteType (Scheme.Hom.fiberToSpecResidueField f s) := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  let _ : IsLocallyNoetherian (Spec (S.residueField s)) := inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (Scheme.Hom.fiberToSpecResidueField f s)

end AlgebraicGeometry.Scheme.Hom
