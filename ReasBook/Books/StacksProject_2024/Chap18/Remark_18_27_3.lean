import Mathlib
import StacksProject_2024.Chap18.Definition_18_31_1

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
  `RingedSite.Hom.(^*)`,
  `MonoidalClosed.curry`,
  `ihom.ev`;
- best owner abstraction: the ambient owner is the pullback functor `(f^*)`; when mathlib's
  Cartesian-closed comparison owner `CategoryTheory.expComparison` is available, this remark is
  its ringed-site component. In the tensor/internal-Hom setting used here, the public declaration
  remains the thin bridge obtained by currying the pullback of evaluation after the monoidal
  comparison of `(f^*)`;
- primitive data: a morphism of ringed sites `f` and two module sheaves `ℱ 𝒢`;
- derived API: the comparison morphism
  `f^*\mathcal H\!\mathit{om}(\mathcal F, \mathcal G) ⟶
    \mathcal H\!\mathit{om}(f^*\mathcal F, f^*\mathcal G)`.

Source/core/bridge triage:
- `source-facing`: the canonical pullback-to-internal-Hom comparison morphism;
- `core/canonical`: the pullback owner `(f^*)`, and, under the stronger Cartesian-closed
  assumptions used by mathlib's generic comparison API, `CategoryTheory.expComparison`;
- `bridge/view`: `pullbackInternalHomComparison`, which packages the comparison at the source
  statement level without exposing extra owner-side ambient assumptions. -/

variable {X Y : RingedSite} (f : X ⟶ Y)
variable [MonoidalCategory (SheafOfModules Y.structureSheaf)]
variable [MonoidalClosed (SheafOfModules Y.structureSheaf)]
variable [MonoidalCategory (SheafOfModules X.structureSheaf)]
variable [MonoidalClosed (SheafOfModules X.structureSheaf)]
variable [(f^*).Monoidal]

/-- Remark 18.27.3: a morphism of ringed sites carries the internal Hom sheaf of two
`\mathcal O_Y`-modules to the internal Hom sheaf of their pullbacks via a canonical comparison
morphism. -/
noncomputable def pullbackInternalHomComparison
    (ℱ 𝒢 : SheafOfModules Y.structureSheaf) :
    (f^*).obj ((ihom ℱ).obj 𝒢) ⟶
      (ihom ((f^*).obj ℱ)).obj ((f^*).obj 𝒢) :=
  MonoidalClosed.curry
    (μ (f^*) ℱ ((ihom ℱ).obj 𝒢) ≫
      (f^*).map ((ihom.ev ℱ).app 𝒢))

end RingedSite.Hom
