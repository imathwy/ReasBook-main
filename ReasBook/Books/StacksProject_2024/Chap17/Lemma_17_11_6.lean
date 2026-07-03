import Mathlib
import StacksProject_2024.Chap17.Definition_17_10_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.11.6:
- primary domain: filtered-colimit presentations of `\mathcal O_X`-modules associated to modules
  over the global-sections ring;
- inspected owner declarations:
  `CategoryTheory.ObjectProperty.ind`,
  `SheafOfModules.isFinitePresentation`,
  `associatedModuleSheaf`,
  `globalSectionsModuleFunctor_preservesColimits`;
- best owner abstraction: the filtered-colimit conclusion should be stated directly in the
  canonical owner form `ind (SheafOfModules.isFinitePresentation (RingedSpace.ringCatSheaf X))`
  on `X.Modules`, rather than by a parallel local predicate that unpacks the same witness data;
- primitive data: the ringed space `X`, the global-sections module `M`, and the source-facing
  isomorphism witness `ℱ ≅ 𝓕_ M`;
- derived API: the `ind` packaging of the filtered-colimit presentation by finitely presented
  module sheaves.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that a module sheaf associated to a global-sections module
  is a filtered colimit of finitely presented `\mathcal O_X`-modules;
- `core/canonical`: `CategoryTheory.ObjectProperty.ind` and
  `SheafOfModules.isFinitePresentation`;
- `bridge/view`: the associated-module-sheaf owner `𝓕_ M`, together with the ambient isomorphism
  witness identifying `ℱ` with that owner.
-/

-- Proof sketch: choose an associated-module-sheaf presentation of `ℱ` from Definition `17.10.6`,
-- then recover a functor realizing that presentation from Lemma `17.10.5`. Apply Lemma
-- `10.11.3` to write `M` as a filtered colimit of finitely presented `R`-modules, then use that
-- the associated-sheaf functor preserves colimits and carries finitely presented modules to
-- finitely presented `\mathcal O_X`-modules.
/-- Lemma 17.11.6: if `ℱ` is an `\mathcal O_X`-module associated to an
`R = \Gamma(X, \mathcal O_X)`-module `M`, then `ℱ` is a directed colimit of finitely presented
`\mathcal O_X`-modules. -/
theorem associatedGlobalSectionsModuleSheaf_isFilteredColimitOfFinitePresentation
    {X : RingedSpace.{u}} (M : ModuleCat (X.presheaf.obj (op ⊤))) (ℱ : X.Modules)
    (hℱ : Nonempty (ℱ ≅ 𝓕_ M)) :
    ind (SheafOfModules.isFinitePresentation (RingedSpace.ringCatSheaf X)) ℱ := sorry

end AlgebraicGeometry
