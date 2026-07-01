import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap21.Lemma_21_12_2

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.11.4:
- primary domain: right derived functors of the canonical inclusion
  `Mod(\mathcal O_X) ⥤ PMod(\mathcal O_X)` and the cohomology presheaf of the underlying abelian
  sheaf;
- sampled owner declarations:
  `RingedSpace.ringCatSheaf`,
  `RingedSpace.Modules`,
  `SheafOfModules.forget`,
  `ringedSiteModuleInclusion_rightDerived_obj_is_cohomologyPresheaf`;
- best owner abstraction: the ringed-site theorem
  `ringedSiteModuleInclusion_rightDerived_obj_is_cohomologyPresheaf`, specialized to the structure
  sheaf `(RingedSpace.ringCatSheaf X)`, together with the canonical instance
  `PreservesFiniteLimits (SheafOfModules.forget (RingedSpace.ringCatSheaf X))`;
- primitive data: a coefficient sheaf `𝒪 : Sheaf J RingCat`, a sheaf of `𝒪`-modules `ℱ`, and a
  cohomological degree `p`;
- derived API here: the ringed-space specialization `𝒪 := (RingedSpace.ringCatSheaf X)`, together with the
  underlying additive presheaf and sheaf obtained from `PresheafOfModules.toPresheaf` and
  `SheafOfModules.toSheaf`.

Source/core/bridge triage:
- `source-facing`: the ringed-space identification between the underlying additive presheaf of the
  derived inclusion and the cohomology presheaf `U ↦ H^p(U, \mathcal F)`;
- `core/canonical`: `SheafOfModules.forget`, the anonymous instance
  `PreservesFiniteLimits (SheafOfModules.forget (RingedSpace.ringCatSheaf X))`, and
  `ringedSiteModuleInclusion_rightDerived_obj_is_cohomologyPresheaf`;
- `bridge/view`: specializing the coefficient sheaf in the canonical ringed-site statement to the
  structure sheaf `(RingedSpace.ringCatSheaf X)`.

This item adds no new owner-level mathematics beyond that canonical ringed-site statement, so the
refined file should recall the owner theorem directly rather than keep a duplicate ringed-space
wrapper.
-/

/- Lemma 20.11.4 is the ringed-space specialization of the canonical ringed-site comparison
between the `p`-th right derived object of `Mod(\mathcal O) ⥤ PMod(\mathcal O)` and the
cohomology presheaf of the underlying additive sheaf. -/
recall ringedSiteModuleInclusion_rightDerived_obj_is_cohomologyPresheaf

section

variable (X : RingedSpace.{u})
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable (F : (RingedSpace.Modules X)) (p : ℕ)

/- Companion recall: the inclusion `Mod(\mathcal O_X) ⥤ PMod(\mathcal O_X)` is left exact in the
canonical owner form `PreservesFiniteLimits (SheafOfModules.forget (RingedSpace.ringCatSheaf X))`. -/
#synth PreservesFiniteLimits (SheafOfModules.forget (RingedSpace.ringCatSheaf X))

/- Source-facing specialization: for a ringed space `X`, an `\mathcal O_X`-module `\mathcal F`,
and a degree `p`, the canonical owner theorem specializes exactly to the comparison stated in
Lemma 20.11.4. -/
#check (ringedSiteModuleInclusion_rightDerived_obj_is_cohomologyPresheaf (RingedSpace.ringCatSheaf X) F p :
  IsIsomorphic
    ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).obj
      (((SheafOfModules.forget (RingedSpace.ringCatSheaf X)).rightDerived p).obj F))
    (((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj F).cohomologyPresheaf p))

end

end AlgebraicGeometry.RingedSpace
