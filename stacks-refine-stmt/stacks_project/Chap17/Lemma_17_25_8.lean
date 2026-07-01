import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap18.Lemma_18_32_5

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.25.8:
- primary domain: categorical smallness of invertible `\mathcal O_X`-modules on a ringed space,
  expressed as a set of representatives up to isomorphism;
- inspected owner declarations:
  `SheafOfModules.RingedSite.exists_set_of_invertible_module_representatives`,
  `SheafOfModules.RingedSite.invertibleModuleProperty_essentiallySmall`,
  `CategoryTheory.ObjectProperty.EssentiallySmall.exists_small`,
  `SheafOfModules.exists_set_of_finiteType_module_representatives`;
- best owner abstraction: the Chapter 18 ringed-site theorem
  `SheafOfModules.RingedSite.exists_set_of_invertible_module_representatives`, specialized to the
  opens site of a ringed space;
- primitive data: a ringed space `X`, equivalently its structure sheaf on `Opens X`;
- derived API: the representative set obtained from the canonical
  `ObjectProperty.EssentiallySmall.exists_small` skeleton construction.

Source/core/bridge triage:
- `source-facing`: the Stacks Project assertion that invertible `\mathcal O_X`-modules admit a
  set of representatives up to isomorphism;
- `core/canonical`: the ringed-site theorem
  `SheafOfModules.RingedSite.exists_set_of_invertible_module_representatives`;
- `bridge/view`: the opens-site specialization from a ringed site to a ringed space.

This item is a canonical-recall item: the ringed-space statement adds no new mathematics beyond
that site-level owner theorem, so the file should reuse the owner directly rather than keeping a
parallel local theorem with the same interface.
-/

/- Lemma 17.25.8: on a ringed space `X`, there is a set of invertible `\mathcal O_X`-modules
containing exactly one representative of each isomorphism class. This is exactly the opens-site
specialization of the canonical ringed-site theorem. -/
recall SheafOfModules.RingedSite.exists_set_of_invertible_module_representatives

end AlgebraicGeometry.RingedSpace
