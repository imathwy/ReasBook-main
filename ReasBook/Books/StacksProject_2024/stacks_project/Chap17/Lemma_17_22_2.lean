import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_5_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_27_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.22.2:
- primary domain: left exactness of internal Hom for sheaves of modules on a ringed space;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `ShortComplex`,
  `ringedSiteModuleInternalHom_exact_in_source`,
  `ringedSiteModuleInternalHom_exact_in_target`;
- best owner abstraction:
  this item is not a new ringed-space owner; it is the opens-site specialization of the Chapter 18
  owner theorems for `ringedSiteModuleCategory`, with coefficient sheaf `X.sheaf`;
- primitive data:
  a short exact sequence `S : ShortComplex (RingedSpace.Modules X)` and a fixed module in the
  remaining internal-Hom variable;
- derived API:
  the two ringed-space exactness clauses obtained by specializing the generic ringed-site theorems.

Source/core/bridge triage:
- `source-facing`: the ringed-space wording of the two exactness statements for internal Hom;
- `core/canonical`: `ringedSiteModuleInternalHom_exact_in_source` and
  `ringedSiteModuleInternalHom_exact_in_target`;
- `bridge/view`: specialization along the opens Grothendieck topology
  `Opens.grothendieckTopology X` and the structure sheaf `X.sheaf`.

The previous local declarations duplicated the Chapter 18 owner theorems at the same mathematical
interface. This file should therefore be a direct recall/use bridge rather than maintain parallel
ringed-space theorem names. -/

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

section Source

variable [BraidedCategory (RingedSpace.Modules X)]

/- Lemma 17.22.2 (1): for a short exact sequence
`0 ⟶ \mathcal F_2 ⟶ \mathcal F_1 ⟶ \mathcal F ⟶ 0` of `\mathcal O_X`-modules, the induced
sequence
`0 ⟶ \mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G) ⟶
\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F_1, \mathcal G) ⟶
\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F_2, \mathcal G)`
is exactly the opens-site specialization of the Chapter 18 owner theorem
`ringedSiteModuleInternalHom_exact_in_source`. -/
#check ringedSiteModuleInternalHom_exact_in_source (Opens.grothendieckTopology X) X.sheaf

end Source

/- Lemma 17.22.2 (2): for a short exact sequence
`0 ⟶ \mathcal G ⟶ \mathcal G_1 ⟶ \mathcal G_2 ⟶ 0` of `\mathcal O_X`-modules, the induced
sequence
`0 ⟶ \mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G) ⟶
\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G_1) ⟶
\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G_2)`
is exactly the opens-site specialization of the Chapter 18 owner theorem
`ringedSiteModuleInternalHom_exact_in_target`. -/
#check ringedSiteModuleInternalHom_exact_in_target (Opens.grothendieckTopology X) X.sheaf

end AlgebraicGeometry.RingedSpace
