import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Lemma_21_34_3_Owner

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SheafOfModules.RingedSite

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.41.3:
- primary domain: tensor-internal-Hom comparison for cochain complexes of module sheaves;
- inspected owner declarations:
  `(ihom M).obj L`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomComparison`;
- best owner abstraction:
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomComparison`;
- primitive data:
  the ambient ringed site together with the three complexes;
- derived API:
  the canonical internal-Hom complex and the assembled tensor-internal-Hom comparison morphism.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.3 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: the ringed-site owner
  `ringedSiteModuleComplexTensorInternalHomComparison`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file should therefore stay at the `bridge/view` layer and directly reuse the owner
declaration instead of duplicating the internal-Hom complex or introducing exact-interface
ringed-space aliases. -/

/- Lemma 20.41.3: for a ringed space `(X, 𝒪_X)` and complexes `𝒦^•`, `𝓛^•`, and `𝓜^•`
of `𝒪_X`-modules, there is a canonical morphism from
`Tot (𝒦^• ⊗_{𝒪_X} Hom^•(𝓜^•, 𝓛^•))` to
`Hom^•(𝓜^•, Tot (𝒦^• ⊗_{𝒪_X} 𝓛^•))`.
In the project API this is the ringed-site tensor-internal-Hom comparison morphism,
specialized to the canonical site of opens of `X`. -/
recall ringedSiteModuleComplexTensorInternalHomComparison

/- Companion check: uncurrying the canonical tensor-internal-Hom comparison recovers the
braiding/evaluation composite already exposed by the ringed-site owner theorem below. -/
recall ringedSiteModuleComplexTensorInternalHomComparison_uncurry

end AlgebraicGeometry.RingedSpace
