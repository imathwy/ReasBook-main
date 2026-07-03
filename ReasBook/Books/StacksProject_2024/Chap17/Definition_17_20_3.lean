import Mathlib
import StacksProject_2024.Chap17.Definition_17_17_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules

variable {X Y : RingedSpace.{u}}

/-
Domain-style sampling for Definition 17.20.3:
- primary domain: relative flatness of an `\mathcal O_X`-module, expressed by restricting scalars
  along the inverse-image structure-sheaf map `f^{-1}\mathcal O_Y \to \mathcal O_X`;
- sampled owner declarations:
  `RingedSpace.Hom.inverseImageStructureSheafHomComm`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.isFlat_stalk`,
  `Module.Flat`;
- owner abstraction: the canonical global owner is
  `SheafOfModules.RingedSite.IsFlat` for the restricted `f^{-1}\mathcal O_Y`-module obtained from
  `ℱ`; the stalkwise condition is companion bridge API;
- primitive data: the sheaf `ℱ`, the morphism `f`, and the restricted `f^{-1}\mathcal O_Y`-module
  structure on `ℱ`;
- derived API: the source-facing predicates `flat_over` and `flat_over_at`, with the latter
  recording the stalkwise view.

Source/core/bridge triage:
- `source-facing`: `flat_over`;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: the restricted module below and the stalkwise predicate `flat_over_at`.

This file should therefore organize relative flatness around the canonical exact-tensor owner on the
restricted `f^{-1}\mathcal O_Y`-module, and keep the stalkwise formulation only as a companion
bridge.
-/

private abbrev relativeModule
    (ℱ : X.Modules) (f : X ⟶ Y) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).map
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f))).obj ℱ

private abbrev relativeStalk
    (ℱ : X.Modules) (f : X ⟶ Y) (x : X) :
    ModuleCat (Y.presheaf.stalk (f.hom.base x)) :=
  (ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj (stalkModuleCat ℱ x)

/-- Definition 17.20.3: an `\mathcal O_X`-module `\mathcal F` is flat over `Y` when, after
restricting scalars along `f^{-1}\mathcal O_Y \to \mathcal O_X`, it is a flat
`f^{-1}\mathcal O_Y`-module in the canonical exact-tensor sense. -/
abbrev flat_over
    (ℱ : X.Modules) (f : X ⟶ Y) : Prop :=
  SheafOfModules.RingedSite.IsFlat
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf)
    (relativeModule ℱ f)

/-- Flatness of `\mathcal F` over `Y` at a point means that the stalk `\mathcal F_x` is flat over
the target stalk `\mathcal O_{Y, f(x)}`. -/
abbrev flat_over_at
    (ℱ : X.Modules) (f : X ⟶ Y) (x : X) : Prop :=
  Module.Flat (Y.presheaf.stalk (f.hom.base x)) ↑(relativeStalk ℱ f x)

/-- Companion bridge: a sheaf is flat over `Y` exactly when its stalks are flat over the target
stalk rings. -/
theorem flat_over_iff_pointwise (ℱ : X.Modules) (f : X ⟶ Y) :
    flat_over ℱ f ↔ ∀ x : X, flat_over_at ℱ f x :=
  sorry

end SheafOfModules
