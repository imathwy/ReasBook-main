import Mathlib
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap17.Definition_17_14_1

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 17.14.6:
- primary domain: finite locally free sheaves of modules on a ringed space and their behavior
  under direct-summand constructions;
- sampled owner declarations:
  `SheafOfModules.IsFiniteLocallyFree`,
  `SheafOfModules.IsLocallyDirectSummandOfFiniteFree`,
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `CategoryTheory.Retract`;
- best owner abstraction: the chapter owner for the local direct-summand condition is
  `SheafOfModules.IsLocallyDirectSummandOfFiniteFree`; a global retract into a finite locally free
  sheaf is only bridge data producing that owner locally;
- primitive data: a module sheaf `ℱ : ModX`, local-ring stalks on `X`, finite presentation of `ℱ`,
  and local retracts of finite free restrictions of `ℱ`;
- derived API: the source-facing global retract theorem below.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that a direct summand of a finite locally free sheaf
  is finite locally free;
- `core/canonical`: `SheafOfModules.IsLocallyDirectSummandOfFiniteFree`;
- `bridge/view`: a global categorical retract `Retract ℱ ℋ` with `ℋ` finite locally free. -/

-- Proof sketch: for each `x : X`, the owner hypothesis gives a neighbourhood `U` on which
-- `ℱ.over U` is a retract of a finite free sheaf. Passing to the stalk at `x`, the stalk module
-- `ℱ_x` is therefore a retract of a finite free module over the local ring `𝒪_{X, x}`, hence is
-- finite free by Algebra, Lemma `10.78.2`. Lemma `17.11.7` then upgrades these stalkwise finite
-- free models to finite free neighbourhoods because `ℱ` is finitely presented.
/-- Owner-level form of Lemma 17.14.6: on a ringed space whose stalk rings are local, a finitely
presented `\mathcal O_X`-module that is locally a direct summand of a finite free module is finite
locally free. -/
theorem isFiniteLocallyFree_of_isLocallyDirectSummandOfFiniteFree_of_stalk_isLocalRing
    (ℱ : ModX) (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x))
    [ℱ.IsFinitePresentation] [ℱ.IsLocallyDirectSummandOfFiniteFree] :
    ℱ.IsFiniteLocallyFree := sorry

-- Proof sketch: a global retract of a finite locally free sheaf restricts on each neighbourhood
-- where `ℋ` is finite free to a local retract of a finite free sheaf, so `ℱ` satisfies the owner
-- predicate `IsLocallyDirectSummandOfFiniteFree`. A retract of a finitely presented sheaf is again
-- finitely presented, so the owner theorem applies.
/-- Lemma 17.14.6: if every stalk `\mathcal O_{X, x}` is a local ring, then any direct summand of
a finite locally free `\mathcal O_X`-module is finite locally free. Here the direct-summand
hypothesis is expressed by a categorical retract. -/
theorem isFiniteLocallyFree_of_retract_of_stalk_isLocalRing
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x))
    {ℱ ℋ : ModX} [ℋ.IsFiniteLocallyFree] (hret : Retract ℱ ℋ) :
    ℱ.IsFiniteLocallyFree := sorry

end SheafOfModules
