import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_34_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SheafOfModules.RingedSite

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.41.5:
- primary domain: tensor-to-iterated-internal-Hom comparison for cochain complexes of
  `𝒪_X`-modules on a ringed space;
- inspected owner declarations:
  `(ihom K).obj L`,
  `ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom`;
- best owner abstraction:
  `ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom`,
  with the iterated internal-Hom target expressed directly through the ringed-site owner layer;
- primitive data:
  the three complexes `K`, `L`, `M` and the ambient monoidal-closed structure on the module
  category;
- derived API:
  the canonical comparison morphism together with its tensor-side uncurrying formula.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.5 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: the ringed-site owner
  `ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file should therefore stay at the `bridge/view` layer and directly reuse the owner
declaration instead of introducing a parallel ringed-space wrapper for the same morphism or its
component formula. -/

/- Lemma 20.41.5: given complexes `𝒦^•`, `𝓛^•`, and
`𝓜^•` of `𝒪_X`-modules on a ringed space `(X, 𝒪_X)`, there is a
canonical morphism
`Tot (Hom^•(𝓛^•, 𝓜^•) ⊗_{𝒪_X} 𝒦^•) ⟶ Hom^•(Hom^•(𝒦^•, 𝓛^•), 𝓜^•)`
of complexes of `𝒪_X`-modules. In the project API this is the ringed-site
tensor-to-iterated-internal-Hom comparison, specialized to the canonical site of opens of `X`. -/
recall ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom

/- Companion recall: uncurrying the canonical tensor-to-iterated-internal-Hom comparison
recovers the tensor-side composition/evaluation composite exposed by the ringed-site owner
theorem below. -/
recall ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom_uncurry

end AlgebraicGeometry.RingedSpace
