import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap13.Lemma_13_20_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

local notation "ModX" => SheafOfModules ((RingedSpace.ringCatSheaf X))
local notation "ModY" => SheafOfModules ((RingedSpace.ringCatSheaf Y))

variable [(RingedSpace.Hom.pushforward f).Additive]

/- Domain-style sampling for 20.3.0.4:
- primary domain: bounded-below derived direct image for sheaves of modules on ringed spaces;
- sampled owner API:
  `RingedSpace.Hom.pushforward`,
  `boundedBelowDerivedCategory`,
  `mapBoundedBelowHomotopyToDerivedBelow`,
  `Functor.totalRightDerived`;
- best owner abstraction: the generic owner `Functor.totalRightDerived`, specialized to the
  bounded-below homotopy-to-derived lift of the Chapter 6 ringed-space module pushforward;
- primitive data: the additive module-pushforward functor
  `RingedSpace.Hom.pushforward f : ModX ⥤ ModY`;
- derived API: the canonical bounded-below right derived functor
  `(mapBoundedBelowHomotopyCategoryToDerivedBelow (RingedSpace.Hom.pushforward f)).totalRightDerived
    (mapBoundedBelowHomotopyToDerivedBelow ModX) (boundedBelowHomotopyQuasiIso ModX) :
    D^+(X) ⥤ D^+(Y)`.

Source/core/bridge triage:
- `source-facing`: the bounded-below derived direct image `Rf_* : D^+(X) ⥤ D^+(Y)`;
- `core/canonical`: `Functor.totalRightDerived`;
- `bridge/view`: the specialization to `f _* = RingedSpace.Hom.pushforward f`.

This item adds no new mathematical data beyond that specialization, so the main entry should be a
direct canonical check rather than local duplicate wrapper definitions. -/

/- 20.3.0.4: for a morphism of ringed spaces `f : X ⟶ Y`, the bounded-below derived direct image
`Rf_*` is obtained by specializing `Functor.totalRightDerived` to the bounded-below
homotopy-to-derived lift of `RingedSpace.Hom.pushforward f`. -/
#check Functor.totalRightDerived

end

end AlgebraicGeometry
