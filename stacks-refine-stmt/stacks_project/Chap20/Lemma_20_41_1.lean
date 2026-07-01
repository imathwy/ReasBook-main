import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap21.Lemma_21_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open SheafOfModules.RingedSite

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.41.1:
- primary domain: internal-Hom complexes and tensor-Hom currying for cochain complexes of
  `\mathcal O_X`-modules;
- inspected owner declarations:
  `ringedSiteModuleComplexInternalHom`,
  `ringedSiteModuleComplexInternalHom_currying_isomorphic`,
  `ringedSiteModuleComplexTensorInternalHomComparison`,
  `ringedSiteModuleComplexTensorTotalizationInternalHomUnit`;
- best owner abstraction:
  `ringedSiteModuleComplexInternalHom`, with the currying theorem
  `ringedSiteModuleComplexInternalHom_currying_isomorphic` as its source-facing derived API;
- primitive data:
  the ambient ringed site and the three cochain complexes;
- derived API:
  the internal-Hom complex itself, the tensor-Hom comparison morphisms, and the currying
  isomorphism.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.1 for complexes of `\mathcal O_X`-modules on a ringed space;
- `core/canonical`: the ringed-site owner `ringedSiteModuleComplexInternalHom` and its currying
  theorem;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

The target file therefore belongs at the `bridge/view` layer and should directly reuse the
ringed-site owner theorem instead of rebuilding a parallel ringed-space internal-Hom complex,
its differential, and the resulting currying statement locally. -/

/- Lemma 20.41.1: for cochain complexes `\mathcal K^\bullet`, `\mathcal L^\bullet`, and
`\mathcal M^\bullet` of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, the nested
internal-Hom complex
`\mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet,
\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal M^\bullet))`
is canonically isomorphic to the internal-Hom complex from the total tensor product
`\mathrm{Tot}(\mathcal K^\bullet \otimes_{\mathcal O_X} \mathcal L^\bullet)` to
`\mathcal M^\bullet`. In the project API this is the ringed-site currying theorem, specialized to
the canonical site of opens of `X`. -/
recall ringedSiteModuleComplexInternalHom_currying_isomorphic

end AlgebraicGeometry.RingedSpace
