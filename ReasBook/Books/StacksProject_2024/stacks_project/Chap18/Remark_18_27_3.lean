import Mathlib
import StacksProject_2024.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open Functor.LaxMonoidal
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Remark 18.27.3:
- primary domain: pullback of internal-Hom sheaves along a morphism of ringed sites;
- sampled owner declarations:
  `CategoryTheory.expComparison`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `RingedSite.Hom.(^*)`,
  `MonoidalClosed.curry`,
  `ihom.ev`;
- best owner abstraction: the ambient owner is the pullback functor `(f^*)`; when mathlib's
  Cartesian-closed comparison owner `CategoryTheory.expComparison` is available, this remark is
  its ringed-site component. In the tensor/internal-Hom setting used here, the public declaration
  remains the thin bridge obtained by currying the pullback of evaluation after the canonical
  lax-monoidal tensor map of `(f^*)`;
- primitive data: a morphism of ringed sites `f` and two module sheaves `ℱ 𝒢`;
- derived API: the comparison morphism
  `f^*\mathcal H\!\mathit{om}(\mathcal F, \mathcal G) ⟶
    \mathcal H\!\mathit{om}(f^*\mathcal F, f^*\mathcal G)`.

Source/core/bridge triage:
- `source-facing`: the canonical pullback-to-internal-Hom comparison morphism;
- `core/canonical`: the pullback owner `(f^*)`, and, under the stronger Cartesian-closed
  assumptions used by mathlib's generic comparison API, `CategoryTheory.expComparison`;
- `bridge/view`: `pullbackInternalHomComparison`, which packages the comparison at the source
  statement level using the canonical inverse-image owner `SheafOfModules.pullback
  f.structureSheafMap` together with its lax-monoidal comparison map. -/

variable {X Y : RingedSite} (f : X ⟶ Y)
variable [MonoidalCategory (SheafOfModules Y.structureSheaf)]
variable [MonoidalClosed (SheafOfModules Y.structureSheaf)]
variable [MonoidalCategory (SheafOfModules X.structureSheaf)]
variable [MonoidalClosed (SheafOfModules X.structureSheaf)]
variable [(SheafOfModules.pullback f.structureSheafMap).LaxMonoidal]

scoped notation:max f:max "^*" => SheafOfModules.pullback (RingedSite.Hom.structureSheafMap f)

open scoped RingedSite.Hom

local notation "ModY" => SheafOfModules Y.structureSheaf
local notation "ModX" => SheafOfModules X.structureSheaf
set_option quotPrecheck false in
local notation A " ⟶[ModY] " B:10 => ((ihom A).obj B)
set_option quotPrecheck false in
local notation A " ⟶[ModX] " B:10 => ((ihom A).obj B)

/-- Remark 18.27.3: a morphism of ringed sites carries the internal Hom sheaf of two
`\mathcal O_Y`-modules to the internal Hom sheaf of their pullbacks via a canonical comparison
morphism. -/
noncomputable abbrev pullbackInternalHomComparison (ℱ 𝒢 : ModY) :
    (f^*).obj (ℱ ⟶[ModY] 𝒢) ⟶ ((f^*).obj ℱ ⟶[ModX] (f^*).obj 𝒢) :=
  MonoidalClosed.curry
    (μ (f^*) ℱ (ℱ ⟶[ModY] 𝒢) ≫
      (f^*).map ((ihom.ev ℱ).app 𝒢))

/-- Uncurrying `pullbackInternalHomComparison` recovers the pullback of evaluation preceded by the
canonical monoidal comparison map for `f^*`. -/
theorem uncurry_pullbackInternalHomComparison (ℱ 𝒢 : ModY) :
    MonoidalClosed.uncurry (pullbackInternalHomComparison f ℱ 𝒢) =
      μ (f^*) ℱ (ℱ ⟶[ModY] 𝒢) ≫ (f^*).map ((ihom.ev ℱ).app 𝒢) := by
  simp [pullbackInternalHomComparison]

end RingedSite.Hom
