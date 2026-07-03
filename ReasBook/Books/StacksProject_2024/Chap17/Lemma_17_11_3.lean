import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap18.Lemma_18_24_1

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Lemma 17.11.3:
- primary domain: finite type and finite presentation for sheaves of modules, specialized in the
  source to `\mathcal O_X`-modules on a ringed space;
- inspected owner declarations:
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.isFiniteType_kernel_of_epi_of_finitePresentation`,
  `SheafOfModules.isFinitePresentation_cokernel`,
  `RingedSpace.ringCatSheaf`;
- best owner abstraction: the generic owner theorem
  `SheafOfModules.isFinitePresentation_cokernel`;
- primitive data: a morphism of sheaves of modules over an ambient sheaf of rings together with
  finite-type and finite-presentation instances on source and target;
- derived API: the finite-presentation instance on the cokernel.

Source/core/bridge triage:
- `source-facing`: the ringed-space formulation of Stacks Project Lemma 17.11.3;
- `core/canonical`: `SheafOfModules.isFinitePresentation_cokernel`;
- `bridge/view`: the ringed-space specialization obtained by instantiating the ambient sheaf of
  rings to `(RingedSpace.ringCatSheaf X)`.
-/

/- Lemma 17.11.3: for a morphism `φ : 𝒢 ⟶ ℱ` of `\mathcal O_X`-modules on a ringed space, if
`𝒢` is of finite type and `ℱ` is finitely presented, then `cokernel φ` is finitely presented.
This is exactly the canonical owner theorem
`SheafOfModules.isFinitePresentation_cokernel`, whose ambient sheaf of rings specializes to
`(RingedSpace.ringCatSheaf X)`.
-/
recall SheafOfModules.isFinitePresentation_cokernel
