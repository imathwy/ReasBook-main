import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Lemma_21_34_3

-- Declarations for this item will be appended below by the statement pipeline.

open SheafOfModules.RingedSite

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.41.3:
- primary domain: tensor-internal-Hom comparison for cochain complexes of module sheaves;
- inspected owner declarations:
  `SheafOfModules.RingedSite.ringedSiteModuleComplexInternalHom`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomComparisonF`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomComparisonComm`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomComparison`;
- best owner abstraction:
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomComparison`;
- primitive data:
  the ambient ringed site together with the three complexes;
- derived API:
  the canonical internal-Hom complex and the assembled tensor-internal-Hom comparison morphism.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.3 for complexes of `\mathcal O_X`-modules on a ringed space;
- `core/canonical`: the ringed-site owner
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomComparison`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file should therefore stay at the `bridge/view` layer and directly recall the owner
declaration instead of duplicating the internal-Hom complex or introducing exact-interface
ringed-space aliases. -/

/- Lemma 20.41.3: for a ringed space `(X, \mathcal O_X)` and complexes
`\mathcal K^\bullet`, `\mathcal L^\bullet`, and `\mathcal M^\bullet` of
`\mathcal O_X`-modules, there is a canonical morphism
`\operatorname{Tot}(\mathcal K^\bullet \otimes_{\mathcal O_X}
  \mathcal H\!\mathit{om}^\bullet(\mathcal M^\bullet, \mathcal L^\bullet))
\to \mathcal H\!\mathit{om}^\bullet(\mathcal M^\bullet,
  \operatorname{Tot}(\mathcal K^\bullet \otimes_{\mathcal O_X} \mathcal L^\bullet))`.
In the project API this is the ringed-site tensor-internal-Hom comparison morphism, specialized to
the canonical site of opens of `X`. -/
recall ringedSiteModuleComplexTensorInternalHomComparison

/- Companion recall: the degreewise components of the tensor-internal-Hom comparison commute with
the differentials before assembling to the morphism above. -/
recall ringedSiteModuleComplexTensorInternalHomComparisonComm

end AlgebraicGeometry.RingedSpace
