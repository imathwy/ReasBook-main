import Mathlib
import stacks_project.Chap20.Lemma_20_11_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.12.2:
- primary domain: sheaves of modules on a ringed space, viewed through their underlying abelian
  sheaves and the flasqueness predicate;
- sampled owner declarations:
  `(RingedSpace.ringCatSheaf X)`,
  `(RingedSpace.Modules X)`,
  `moduleUnderlyingSheaf`,
  `TopCat.Sheaf.IsFlasque`;
- best owner abstraction: the Chapter 20 ringed-space owner `(RingedSpace.Modules X)`, with
  `moduleUnderlyingSheaf` as the canonical bridge to the flasque sheaf statement;
- primitive data: a ringed space `X`, an object `ℐ : (RingedSpace.Modules X)`, and the categorical
  injectivity hypothesis `Injective ℐ`;
- derived API: flasqueness of the underlying abelian sheaf.

Source/core/bridge triage:
- `source-facing`: the statement that injective `\mathcal O_X`-modules are flasque;
- `core/canonical`: `(RingedSpace.Modules X)` and `TopCat.Sheaf.IsFlasque`;
- `bridge/view`: `moduleUnderlyingSheaf`.

This file should therefore reuse the earlier Chapter 20 owner declarations rather than duplicate a
local `ringedSpaceRingCatSheaf` abbreviation. -/

-- Proof sketch: by the flasqueness owner API from Definition `20.12.1`, it suffices to show that
-- every restriction morphism of the underlying additive sheaf is epi. For `AddCommGrpCat` this is
-- equivalent to surjectivity, and Lemma `20.8.1` supplies that surjectivity for injective
-- `\mathcal O_X`-modules.
/-- Lemma 20.12.2: for a ringed space `(X, \mathcal{O}_X)`, any injective `\mathcal{O}_X`-module
is flasque as a sheaf of abelian groups. -/
theorem module_isFlasque_of_injective
    {X : RingedSpace.{u}} (ℐ : (RingedSpace.Modules X))
    (hℐ : Injective ℐ) :
    TopCat.Sheaf.IsFlasque (moduleUnderlyingSheaf ℐ) := sorry

end AlgebraicGeometry.RingedSpace
