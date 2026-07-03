import Mathlib.Tactic.Recall
import StacksProject_2024.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Definition 20.26.15:
- primary domain: Tor objects of sheaves of modules on a ringed space;
- sampled owner declarations:
  `CategoryTheory.Tor`,
  `Functor.leftDerived`,
  `MonoidalCategory.tensoringLeft`;
- best owner abstraction: the public owner for `\operatorname{Tor}_p^{\mathcal O_X}` is the
  canonical bifunctor `CategoryTheory.Tor (RingedSpace.Modules X) p`;
- primitive vs derived: the primitive data is only the pair of module objects `\mathcal F`,
  `\mathcal G`; the Tor bifunctor is the owner abstraction, while tensoring in one variable and
  left derivation are already canonical derived API behind that owner.

Source/core/bridge triage:
- `source-facing`: the evaluated object `(((Tor (RingedSpace.Modules X) p).obj ℱ).obj 𝒢)`;
- `core/canonical`: `CategoryTheory.Tor`;
- `bridge/view`: none needed in this file, since the numbered item is just the canonical Tor
  object specialized to `(RingedSpace.Modules X)`. -/

recall CategoryTheory.Tor

section

variable {X : RingedSpace}
variable [Abelian (RingedSpace.Modules X)]
local instance : Preadditive (RingedSpace.Modules X) := (inferInstance : Abelian (RingedSpace.Modules X)).toPreadditive
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasProjectiveResolutions (RingedSpace.Modules X)]
variable (p : ℕ)

/- Definition 20.26.15: for a ringed space `(X, \mathcal O_X)`, the owner of
`\operatorname{Tor}_p^{\mathcal O_X}` on `\mathcal O_X`-modules is the canonical bifunctor
`CategoryTheory.Tor` on the monoidal abelian category `(RingedSpace.Modules X)`. -/
#check (Tor (RingedSpace.Modules X) p)

variable (ℱ 𝒢 : (RingedSpace.Modules X))

/- Companion recall: evaluating the canonical Tor bifunctor at `\mathcal F` and `\mathcal G`
gives the source object `\operatorname{Tor}_p^{\mathcal O_X}(\mathcal F, \mathcal G)`, which the
text describes as `H^{-p}(\mathcal F \otimes_{\mathcal O_X}^{\mathbf L} \mathcal G)`. -/
#check ((((Tor (RingedSpace.Modules X) p).obj ℱ).obj 𝒢) : (RingedSpace.Modules X))

end

end AlgebraicGeometry.RingedSpace
