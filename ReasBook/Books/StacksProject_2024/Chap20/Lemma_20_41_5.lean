import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Lemma_21_34_5

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.41.5:
- primary domain: tensor-to-iterated-internal-Hom comparison for cochain complexes of
  `\mathcal O_X`-modules on a ringed space;
- inspected owner declarations:
  `SheafOfModules.RingedSite.ringedSiteModuleComplexInternalHom`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomToIteratedInternalHomComponent`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom`,
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom_f`;
- best owner abstraction:
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom`,
  with the iterated internal-Hom target and its degreewise formula derived from the same
  ringed-site owner layer;
- primitive data:
  the three complexes `K`, `L`, `M` and the ambient monoidal-closed structure on the module
  category;
- derived API:
  the canonical comparison morphism and its degree-`n` component formula.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.5 for complexes of `\mathcal O_X`-modules on a ringed space;
- `core/canonical`: the ringed-site owner
  `SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file should therefore stay at the `bridge/view` layer and directly reuse the owner
declaration instead of introducing a parallel ringed-space wrapper for the same morphism or its
component formula. -/

/- Lemma 20.41.5: given complexes `\mathcal K^\bullet`, `\mathcal L^\bullet`, and
`\mathcal M^\bullet` of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, there is a
canonical morphism
`\operatorname{Tot}(\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal M^\bullet)
  \otimes_{\mathcal O_X} \mathcal K^\bullet)
\to \mathcal H\!\mathit{om}^\bullet(\mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet,
  \mathcal L^\bullet), \mathcal M^\bullet)`
of complexes of `\mathcal O_X`-modules. In the project API this is the ringed-site
tensor-to-iterated-internal-Hom comparison, specialized to the canonical site of opens of `X`. -/
recall SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom

/- Companion recall: the degree-`n` component formula for the ringed-space specialization is the
specialized form of the ringed-site statement below. -/
recall SheafOfModules.RingedSite.ringedSiteModuleComplexTensorInternalHomToIteratedInternalHom_f

end AlgebraicGeometry.RingedSpace
