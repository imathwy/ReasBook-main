import Mathlib
import StacksProject_2024.Chap17.Definition_17_25_1
import StacksProject_2024.Chap18.Lemma_18_32_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y
local notation "IsInvertibleX" =>
  @SheafOfModules.RingedSite.IsInvertible _ _ (Opens.grothendieckTopology X) X.sheaf _ _
local notation "IsInvertibleY" =>
  @SheafOfModules.RingedSite.IsInvertible _ _ (Opens.grothendieckTopology Y) Y.sheaf _ _

/- Domain-style sampling for Lemma 17.25.3:
- primary domain: invertible `\mathcal O_X`-modules under pullback along a morphism of ringed
  spaces;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsInvertible`,
  `AlgebraicGeometry.RingedSpace.Hom.pullback`,
  `SheafOfModules.RingedSite.pullback_isInvertible`,
  `SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse`;
- best owner abstraction: the canonical owner is `SheafOfModules.RingedSite.IsInvertible`,
  specialized to `RingedSpace.Modules`; the source-facing pullback statement is therefore a
  ringed-space specialization of the Chapter 18 ringed-site theorem, not a separate existential
  tensor-inverse wrapper;
- primitive data: a morphism of ringed spaces `f : X ⟶ Y` and a module `ℒ : Y.Modules`;
- derived API: the theorem and global instance asserting that the pullback
  `(RingedSpace.Hom.pullback f).obj ℒ` is invertible whenever `ℒ` is.

Source/core/bridge triage:
- `source-facing`: invertibility of the pulled-back module on a ringed space;
- `core/canonical`: `SheafOfModules.RingedSite.IsInvertible` and the pullback owner
  `RingedSpace.Hom.pullback`;
- `bridge/view`: the specialization of
  `SheafOfModules.RingedSite.pullback_isInvertible` from ringed sites to ringed spaces.
-/

variable [MonoidalCategory X.Modules] [MonoidalCategory Y.Modules]

-- Proof sketch: this is the Chapter 18 pullback-preserves-invertibility theorem specialized from
-- ringed sites to the opens site of a ringed space.
/-- Lemma 17.25.3: for a morphism of ringed spaces `f : (X, \mathcal O_X) → (Y, \mathcal O_Y)`,
the pullback of an invertible `\mathcal O_Y`-module is invertible. -/
theorem pullback_isInvertible
    (f : X ⟶ Y)
    (ℒ : ModY)
    [IsInvertibleY ℒ] :
    IsInvertibleX ((f^*).obj ℒ) := by
  simpa using
    (SheafOfModules.RingedSite.pullback_isInvertible
      (Opens.map f.hom.base)
      (RingedSpace.Hom.toRingCatSheafHom f)
      ℒ)

instance instIsInvertiblePullback
    (f : X ⟶ Y)
    (ℒ : ModY)
    [IsInvertibleY ℒ] :
    IsInvertibleX ((f^*).obj ℒ) :=
  pullback_isInvertible f ℒ

end AlgebraicGeometry.RingedSpace
