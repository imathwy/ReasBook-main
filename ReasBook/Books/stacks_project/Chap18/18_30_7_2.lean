import Mathlib.Tactic.Recall
import stacks_project.Chap18.Lemma_18_30_7

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for 18.30.7.2:
- primary domain: finite basis cokernel presentations of sheaves of modules on a ringed site by
  sums of the standard modules `j_{U!}\mathcal O_U`;
- sampled relevant declarations:
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero`,
  `CategoryTheory.Limits.cokernel`,
  `SheafOfModules.RingedSite.exists_epi_from_coproduct_basis_localizedStructureModuleExtensionByZero`,
  `SheafOfModules.RingedSite.HasFiniteBasisConstructibleModuleCokernelPresentation`;
- best owner abstraction: the source-facing owner is
  `SheafOfModules.RingedSite.HasFiniteBasisConstructibleModuleCokernelPresentation`; the finite
  coproduct and cokernel constructions belong to the core implementation layer of that owner;
- primitive data: a basis `B`, finite families `U`, `V`, a morphism between the corresponding
  finite coproducts of `localizedStructureModuleExtensionByZero 𝒪`, an isomorphism
  `ℱ ≅ cokernel f`, and the conditions `U i ∈ B`, `V j ∈ B`;
- derived API: the ambient finite-coproduct and cokernel constructions used inside the
  presentation predicate.

Source/core/bridge triage:
- `source-facing`:
  `SheafOfModules.RingedSite.HasFiniteBasisConstructibleModuleCokernelPresentation`;
- `core/canonical`: `localizedStructureModuleExtensionByZero 𝒪 U`, finite coproducts, and
  `cokernel`;
- `bridge/view`: none. This numbered item should recall the source-facing presentation predicate
  itself, not only the ingredient-level owners appearing inside it.
-/

/- 18.30.7.2: an `\mathcal O`-module admits a finite basis cokernel presentation in the
source-facing sense recorded by
`SheafOfModules.RingedSite.HasFiniteBasisConstructibleModuleCokernelPresentation`; this keeps the
basis parameter `B`, the finite families `U` and `V`, the presentation morphism, the isomorphism
with its cokernel, and the conditions `U i ∈ B`, `V j ∈ B` on the public surface. -/
recall SheafOfModules.RingedSite.HasFiniteBasisConstructibleModuleCokernelPresentation
