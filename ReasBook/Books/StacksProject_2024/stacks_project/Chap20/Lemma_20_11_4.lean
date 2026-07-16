import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap06.RingedSpaceModuleCore
import StacksProject_2024.stacks_project.Chap21.Lemma_21_12_2

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.11.4:
- primary domain: right derived functors of the canonical inclusion
  `Mod(𝒪_X) ⥤ PMod(𝒪_X)` and the cohomology presheaf of the underlying abelian
  sheaf;
- sampled owner declarations:
  `RingedSpace.ringCatSheaf`,
  `RingedSpace.Modules`,
  `SheafOfModules.cohomologyPresheaf`,
  `SheafOfModules.cohomologyPresheaf_toPresheaf_isomorphic`;
- best owner abstraction: the ringed-site owner
  `SheafOfModules.cohomologyPresheaf`, specialized to the structure sheaf
  `(RingedSpace.ringCatSheaf X)`, together with the canonical bridge
  `SheafOfModules.cohomologyPresheaf_toPresheaf_isomorphic` and the canonical instance
  `PreservesFiniteLimits (SheafOfModules.forget (RingedSpace.ringCatSheaf X))`;
- primitive data: a coefficient sheaf `𝒪 : Sheaf J RingCat`, a sheaf of `𝒪`-modules `ℱ`, and a
  cohomological degree `p`;
- derived API here: the ringed-space specialization `𝒪 := (RingedSpace.ringCatSheaf X)`,
  together with the underlying additive presheaf and sheaf obtained from
  `PresheafOfModules.toPresheaf` and `SheafOfModules.toSheaf`.

Source/core/bridge triage:
- `source-facing`: the ringed-space identification between the underlying additive presheaf of the
  module-valued cohomology presheaf and the cohomology presheaf `U ↦ H^p(U, 𝓕)`;
- `core/canonical`: `SheafOfModules.cohomologyPresheaf`, `SheafOfModules.forget`, and the
  anonymous instance
  `PreservesFiniteLimits (SheafOfModules.forget (RingedSpace.ringCatSheaf X))`, and
  `SheafOfModules.cohomologyPresheaf_toPresheaf_isomorphic`;
- `bridge/view`: specializing the coefficient sheaf in the canonical ringed-site statement to the
  structure sheaf `(RingedSpace.ringCatSheaf X)`.

This item adds no new owner-level mathematics beyond that canonical ringed-site statement, so the
refined file should recall the owner theorem directly rather than keep a duplicate ringed-space
wrapper.
-/

/- Lemma 20.11.4 is the ringed-space specialization of the canonical bridge from the
module-valued cohomology presheaf to the cohomology presheaf of the underlying additive sheaf. -/
recall SheafOfModules.cohomologyPresheaf_toPresheaf_isomorphic

section

variable (X : RingedSpace.{u})
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable (𝓕 : X.Modules) (p : ℕ)

/- Companion recall: the inclusion `Mod(𝒪_X) ⥤ PMod(𝒪_X)` is left exact in the
canonical owner form `PreservesFiniteLimits (SheafOfModules.forget (ringCatSheaf X))`. -/
#synth PreservesFiniteLimits (SheafOfModules.forget X.ringCatSheaf)

/- Source-facing specialization: for a ringed space `X`, an `𝒪_X`-module `𝓕`,
and a degree `p`, the canonical owner theorem specializes exactly to the comparison stated in
Lemma 20.11.4. -/
#check SheafOfModules.cohomologyPresheaf_toPresheaf_isomorphic X.ringCatSheaf 𝓕 p

end

end AlgebraicGeometry.RingedSpace
