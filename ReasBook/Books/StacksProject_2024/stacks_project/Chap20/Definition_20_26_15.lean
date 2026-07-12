import Mathlib.Tactic.Recall
import StacksProject_2024.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.Chap21.Definition_21_17_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open scoped RingedSiteTor

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Definition 20.26.15:
- primary domain: Tor objects of sheaves of modules on a ringed space;
- sampled owner declarations:
  `CategoryTheory.Tor`,
  `SheafOfModules.RingedSite.tor`,
  `Functor.leftDerived`,
  `MonoidalCategory.tensoringLeft`;
- best owner abstraction: the public owner for the `p`-th Tor object of `𝒪_X`-modules is the
  canonical bifunctor `CategoryTheory.Tor X.Modules p`, and the reusable source-facing object
  surface is already the Chapter 21 ringed-site specialization `Tor[p](ℱ, 𝒢)`;
- primitive vs derived: the primitive data is only the pair of module objects `\mathcal F`,
  `\mathcal G`; the Tor bifunctor is the owner abstraction, while tensoring in one variable and
  left derivation are already canonical derived API behind that owner.

Source/core/bridge triage:
- `source-facing`: the ringed-space Tor object `Tor[p](ℱ, 𝒢)`;
- `core/canonical`: `CategoryTheory.Tor`;
- `bridge/view`: the opens-ringed-site specialization already exported by
  `SheafOfModules.RingedSite.tor`, reused here through the identification
  `RingedSpace.Modules X = ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf`.

This file should therefore recall the owner declaration directly and keep the ringed-space
specialization only as a thin companion. -/

recall CategoryTheory.Tor

section

variable {X : RingedSpace}
variable [MonoidalCategory X.Modules]
variable [MonoidalPreadditive X.Modules]
variable [HasProjectiveResolutions X.Modules]

local notation "Mod" => X.Modules
variable (p : ℕ)

/- Definition 20.26.15: for a ringed space `(X, 𝒪_X)`, the owner of the `p`-th Tor object on
`𝒪_X`-modules is the canonical bifunctor
`CategoryTheory.Tor` on the monoidal category `X.Modules`. -/
#check (Tor Mod p)

variable (ℱ 𝒢 : Mod)

/- Companion recall: evaluating the canonical Tor bifunctor at `ℱ` and `𝒢`
gives the source object `Tor[p](ℱ, 𝒢)`, which the text describes as
`H^{-p}(ℱ ⊗^L 𝒢)`. The
Chapter 21 ringed-site specialization `Tor[p](ℱ, 𝒢)` is the reusable source-facing surface for
this object on a ringed space. -/
#check (Tor[p](ℱ, 𝒢) : Mod)

end

end AlgebraicGeometry.RingedSpace
