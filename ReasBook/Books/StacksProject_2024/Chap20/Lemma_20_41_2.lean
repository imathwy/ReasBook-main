import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Lemma_21_34_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace AlgebraicGeometry.RingedSpace

open SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 20.41.2:
- primary domain: composition pairing for internal-Hom complexes of module-sheaf cochain
  complexes;
- inspected owner declarations:
  `SheafOfModules.RingedSite.internalHomComplexComposition`,
  `SheafOfModules.RingedSite.internalHomComplexComposition_f`;
- best owner abstraction:
  `SheafOfModules.RingedSite.internalHomComplexComposition`, whose source is already the canonical
  tensor product of the two ringed-site internal-Hom complexes;
- primitive data:
  the ambient ringed site and the three cochain complexes;
- derived API:
  the assembled composition morphism and its degreewise formula.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.2 for complexes of `\mathcal O_X`-modules on a ringed space;
- `core/canonical`: the ringed-site owner
  `SheafOfModules.RingedSite.internalHomComplexComposition`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file should therefore stay at the `bridge/view` layer and directly recall the owner
declaration instead of duplicating its internal-Hom complex, tensor source, and componentwise
construction locally. -/

/- Lemma 20.41.2: for a ringed space `(X, \mathcal O_X)` and complexes
`\mathcal K^\bullet`, `\mathcal L^\bullet`, and `\mathcal M^\bullet` of
`\mathcal O_X`-modules, there is a canonical morphism
`\operatorname{Tot}(\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal M^\bullet)
  \otimes_{\mathcal O_X}
  \mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet, \mathcal L^\bullet))
\to \mathcal H\!\mathit{om}^\bullet(\mathcal K^\bullet, \mathcal M^\bullet)`.
This item adds no new owner-level data beyond the canonical ringed-site composition morphism, so
the refined bridge file recalls that owner declaration directly. -/
recall internalHomComplexComposition

/- Companion recall: the degree-`n` component formula for the ringed-space specialization is the
specialized form of the ringed-site statement below. -/
recall internalHomComplexComposition_f

end AlgebraicGeometry.RingedSpace
