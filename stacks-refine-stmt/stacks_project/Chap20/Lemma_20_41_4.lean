import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap21.Lemma_21_34_4

-- Declarations for this item will be appended below by the statement pipeline.

open SheafOfModules.RingedSite

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.41.4:
- primary domain: the tensor-internal-Hom unit for cochain complexes of module sheaves on a
  ringed site;
- inspected owner declarations:
  `ringedSiteModuleComplexTensorTotalizationInternalHomUnitComponent`,
  `ringedSiteModuleComplexTensorTotalizationInternalHomUnit`,
  `ringedSiteModuleComplexTensorTotalizationInternalHomUnitNaturalLeft`,
  `ringedSiteModuleComplexTensorTotalizationInternalHomUnitNaturalRight`;
- best owner abstraction:
  `ringedSiteModuleComplexTensorTotalizationInternalHomUnit`, with the two naturality theorems as
  its derived functorial API;
- primitive data:
  the ambient ringed site and the two cochain complexes `K` and `L`;
- derived API:
  the assembled canonical morphism
  `K ⟶ ringedSiteModuleComplexInternalHom L (HomologicalComplex.tensorObj K L)` and its left/right
  naturality laws.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.4 for complexes of `\mathcal O_X`-modules on a ringed space;
- `core/canonical`: the ringed-site owner
  `ringedSiteModuleComplexTensorTotalizationInternalHomUnit`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file should therefore stay at the `bridge/view` layer and directly recall the ringed-site
owner and its companion naturality lemmas, rather than rebuilding a parallel ringed-space
construction. -/

/- Lemma 20.41.4: for complexes `\mathcal K^\bullet` and `\mathcal L^\bullet` of
`\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, there is a canonical morphism
`\mathcal K^\bullet \to \mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet,
\mathrm{Tot}(\mathcal K^\bullet \otimes_{\mathcal O_X} \mathcal L^\bullet))`
of complexes of `\mathcal O_X`-modules. In the project API this is the ringed-site tensor-Hom
unit, specialized to the Grothendieck topology of opens of `X`. -/
recall ringedSiteModuleComplexTensorTotalizationInternalHomUnit

/- Companion recall: functoriality of the canonical tensor-Hom unit in the left complex is the
specialized form of the ringed-site naturality theorem below. -/
recall ringedSiteModuleComplexTensorTotalizationInternalHomUnitNaturalLeft

/- Companion recall: functoriality of the canonical tensor-Hom unit in the right complex is the
specialized form of the ringed-site naturality theorem below. -/
recall ringedSiteModuleComplexTensorTotalizationInternalHomUnitNaturalRight

end AlgebraicGeometry.RingedSpace
