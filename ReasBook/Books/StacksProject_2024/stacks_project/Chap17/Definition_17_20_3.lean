import Mathlib
import StacksProject_2024.Chap06.Lemma_6_21_5
import StacksProject_2024.Chap17.Definition_17_17_1
import StacksProject_2024.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory
open SheafOfModules.RingedSite (restrictionAlong)

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
  `SheafOfModules.RingedSite.restrictionAlong`,
  `SheafOfModules.IsFlat`,
  `SheafOfModules.flat_at`,
  `TopCat.Sheaf.stalkPullbackIso`,
  `Module.Flat`;
- owner abstraction: by the chapter-local natural-growth priority, the owner is flatness of the
  restricted `f^{-1}\mathcal O_Y`-module in the earlier ringed-space class
  `SheafOfModules.IsFlat`; the source-facing pointwise predicate `flat_over_at` remains the
  stalkwise view, while the main global entry should be direct canonical reuse of that owner via
  the canonical restricted module `relativeModule ℱ f`;
- primitive data: the sheaf `ℱ`, the morphism `f`, and the target point `x`;
- derived API: the canonical restricted module `relativeModule`, the source-facing pointwise
  predicate `flat_over_at`, and the public stalkwise bridge.

Source/core/bridge triage:
- `source-facing`: `flat_over_at`;
- `core/canonical`: `SheafOfModules.IsFlat`, `restrictionAlong`,
  `TopCat.Sheaf.stalkPullbackIso`, and `Module.Flat`;
- `bridge/view`: the restricted module `relativeModule`, the target-stalk module obtained from the
  canonical pullback-stalk isomorphism, and the comparison with the ringed-space predicate
  `flat_at`.

This file should therefore keep the source-facing pointwise predicate over the actual target stalk
`\mathcal O_{Y, f(x)}` and expose the global notion only by direct canonical reuse of flatness of
the restricted `f^{-1}\mathcal O_Y`-module in the Chapter 17 ringed-space owner, with no separate
public ringed-space wrapper around `f^{-1}\mathcal O_Y`.
-/

/-- The `\mathcal O_X`-module `ℱ`, viewed by restriction of scalars as an
`f^{-1}\mathcal O_Y`-module. -/
abbrev relativeModule
    (ℱ : X.Modules) (f : X ⟶ Y) :
    RingedSpace.Modules
      { carrier := X
        presheaf := ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf).presheaf
        IsSheaf := ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf).2 } :=
  (restrictionAlong (RingedSpace.Hom.inverseImageStructureSheafHomComm f)).obj ℱ

private abbrev targetStalkModule
    (ℱ : X.Modules) (f : X ⟶ Y) (x : X) :
    ModuleCat (Y.presheaf.stalk (f.hom.base x)) :=
  (ModuleCat.restrictScalars
    (CategoryTheory.Iso.commRingCatIsoToRingEquiv
      (TopCat.Sheaf.stalkPullbackIso f.hom.base Y.sheaf x)).toRingHom).obj
    (stalkModuleCat (relativeModule ℱ f) x)

/-- Flatness of `\mathcal F` over `Y` at a point means that the stalk `\mathcal F_x` is flat over
the target stalk `\mathcal O_{Y, f(x)}`. -/
abbrev flat_over_at
    (ℱ : X.Modules) (f : X ⟶ Y) (x : X) : Prop :=
  Module.Flat (Y.presheaf.stalk (f.hom.base x)) ↑(targetStalkModule ℱ f x)

variable (ℱ : X.Modules) (f : X ⟶ Y)

/- Definition 17.20.3: an `\mathcal O_X`-module `\mathcal F` is flat over `Y` exactly when the
restricted `f^{-1}\mathcal O_Y`-module is flat in the canonical Chapter 17 owner
`SheafOfModules.IsFlat`. -/
#check ((relativeModule ℱ f).IsFlat)

variable {ℱ : X.Modules} {f : X ⟶ Y}

/-- Companion bridge: the source-facing target-stalk predicate agrees with the canonical pointwise
flatness predicate on the ringed-space view of the restricted `f^{-1}\mathcal O_Y`-module. -/
theorem flat_over_at_iff_relativeModule_flat_at
    (ℱ : X.Modules) (f : X ⟶ Y) (x : X) :
    flat_over_at ℱ f x ↔ (relativeModule ℱ f).flat_at x := sorry

/-- Companion bridge: the canonical restricted-module flatness owner is equivalent to the textbook
pointwise condition via the standard flatness-on-stalks bridge for the restricted
`f^{-1}\mathcal O_Y`-module. -/
theorem flat_over_iff_stalkwise
    (ℱ : X.Modules) (f : X ⟶ Y) :
    (relativeModule ℱ f).IsFlat ↔ ∀ x : X, flat_over_at ℱ f x := by
  constructor
  · intro hflat x
    exact (flat_over_at_iff_relativeModule_flat_at ℱ f x).2 (hflat.flatAt x)
  · intro hflat
    refine isFlat_of_stalkwise (relativeModule ℱ f) ?_
    intro x
    exact (flat_over_at_iff_relativeModule_flat_at ℱ f x).1 (hflat x)

end SheafOfModules
