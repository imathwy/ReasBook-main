import Mathlib
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap18.Definition_18_32_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Definition 17.25.9:
- primary domain: Picard groups of ringed spaces, viewed through the monoidal category of
  `\mathcal O_X`-modules;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `ringedSitePicardGroup`,
  `Pic(𝒪)`,
  `X.sheaf`;
- best owner abstraction: the core owner is the ringed-site Picard group
  `ringedSitePicardGroup`; the Chapter 17 source-facing surface should therefore be only the
  ringed-space notation `Pic(X)`, defined directly from the structure sheaf of `X`, rather than
  a parallel local owner one bridge lower than the canonical declaration;
- primitive data: the ringed space `X`, equivalently its structure sheaf `X.sheaf`;
- derived API: the ringed-space module category `RingedSpace.Modules X` and the source-facing
  notation `Pic(X)`.

Layer triage:
- `source-facing`: the textbook notation `\mathrm{Pic}(X)`, surfaced here as `Pic(X)`;
- `core/canonical`: `ringedSitePicardGroup (Opens.grothendieckTopology X) X.sheaf`;
- `bridge/view`: the ringed-space module owner `RingedSpace.Modules X` together with the notation
  bridge `Pic(X)`.
-/

variable (X : RingedSpace)
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules X)]

/- Textbook notation for the Picard group `\mathrm{Pic}(X)` of a ringed space, as the canonical
ringed-site Picard group of its structure sheaf. -/
scoped[RingedSpacePicard] notation:max "Pic(" X ")" =>
  _root_.ringedSitePicardGroup (Opens.grothendieckTopology X)
    (SheafedSpace.sheaf X)

open scoped RingedSpacePicard

/- Definition 17.25.9: the Picard group `\mathrm{Pic}(X)` of a ringed space is the canonical
ringed-site Picard group of its structure sheaf, i.e. the abelian group of isomorphism classes of
invertible `\mathcal O_X`-modules under tensor product. -/
#check Pic(X)

end AlgebraicGeometry.RingedSpace
