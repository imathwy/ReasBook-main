import StacksProject_2024.stacks_project.Chap17.Lemma_17_10_4
import StacksProject_2024.stacks_project.Chap31.Definition_31_7_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_8_1
import StacksProject_2024.stacks_project.Chap31.Lemma_31_5_8

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

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

local notation:max ℱ:max " |[" f "," s "]" =>
  ((Scheme.Modules.pullback (Scheme.Hom.fiberι f s)).obj ℱ)

theorem fiber_associatedPoints_eq_weakAss_of_locallyOfFiniteType_probe
    (f : X ⟶ S) [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] (s : S) :
    (ℱ |[f, s]).associatedPoints = (ℱ |[f, s]).weakAss := by
  letI : (ℱ |[f, s]).IsQuasicoherent := by
    simpa using ringedSpaceModulePullback_isQuasicoherent (Scheme.Hom.fiberι f s) ℱ
  let _ : IsLocallyNoetherian (Scheme.Hom.fiber f s) :=
    Scheme.Hom.fiber_isLocallyNoetherian_of_locallyOfFiniteType_probe f s
  exact associatedPoints_eq_weakAss_of_isLocallyNoetherian (ℱ |[f, s])

end AlgebraicGeometry.Scheme.Modules
