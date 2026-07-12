import Mathlib.Tactic.Recall
import StacksProject_2024.Chap17.Lemma_17_11_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 18.24.2:
- primary domain: finite type and finite presentation for sheaves of modules over a sheaf of
  rings on a site, with the source phrased for `\mathcal O`-modules on a ringed site;
- inspected owner declarations:
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.isFinitePresentation_cokernel`,
  `SheafOfModules.isFiniteType_kernel_of_epi_of_finitePresentation`;
- best owner abstraction:
  the generic owner theorem
  `SheafOfModules.isFiniteType_kernel_of_epi_of_finitePresentation` in the ambient category
  `SheafOfModules 𝒪`;
- primitive data:
  a morphism `θ : 𝒢 ⟶ ℱ` together with `[Epi θ]`, `[𝒢.IsFiniteType]`, and
  `[ℱ.IsFinitePresentation]`;
- derived API:
  the finite-type instance on `kernel θ`.

Source/core/bridge triage:
- `source-facing`: the ringed-site formulation of Stacks Project Lemma 18.24.2;
- `core/canonical`: `SheafOfModules.isFiniteType_kernel_of_epi_of_finitePresentation`;
- `bridge/view`: none is needed here, since the chapter statement is already exactly the generic
  owner theorem specialized to the ambient sheaf of rings.

This item is therefore a canonical recall item: the file should reuse the owner theorem directly
instead of introducing a parallel ringed-site-local wrapper. -/

/- Lemma 18.24.2: for a surjective morphism `θ : 𝒢 ⟶ ℱ` of `\mathcal O`-modules on a ringed
site, if `ℱ` is finitely presented and `𝒢` is of finite type, then `kernel θ` is of finite type.
This is already the owner-level theorem
`SheafOfModules.isFiniteType_kernel_of_epi_of_finitePresentation`. -/
recall SheafOfModules.isFiniteType_kernel_of_epi_of_finitePresentation
