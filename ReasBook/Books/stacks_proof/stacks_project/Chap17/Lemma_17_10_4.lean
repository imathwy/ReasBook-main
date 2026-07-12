import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap18.Lemma_18_23_4

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.10.4:
- primary domain: quasi-coherent module sheaves on ringed spaces and their behavior under the
  canonical pullback functor;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsQuasicoherent`,
  `RingedSpace.Hom.pullback`,
  `SheafOfModules.RingedSite.pullback_isQuasicoherent`,
  `RingedSpace.Hom.pullback_isFiniteType`;
- best owner abstraction: the Chapter 18 owner theorem
  `SheafOfModules.RingedSite.pullback_isQuasicoherent`, specialized to the ringed site of opens of
  a ringed space, together with the owner predicate `SheafOfModules.IsQuasicoherent` on
  `RingedSpace.Modules Y`;
- primitive data: a morphism of ringed spaces `f : X ⟶ Y` and a module sheaf
  `𝒢 : RingedSpace.Modules Y`;
- derived API: the source-facing ringed-space specialization asserting that pullback carries
  quasi-coherent modules to quasi-coherent modules.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that pullback preserves quasi-coherence;
- `core/canonical`: `SheafOfModules.RingedSite.pullback_isQuasicoherent`,
  `SheafOfModules.IsQuasicoherent`, and the pullback owner `f^*`;
- `bridge/view`: the specialization along `Opens.map f.hom.base` and
  `RingedSpace.Hom.toRingCatSheafHom f`, matching the Chapter 17 ringed-space pullback bridge
  pattern.
-/

variable {X Y : RingedSpace.{u}}

-- Proof sketch: this is the ringed-space specialization of the Chapter 18 owner theorem on
-- pullback preserving quasi-coherence for sheaves of modules on ringed sites, applied to the site
-- of opens of `Y` and `X` and the canonical structure-sheaf map
-- `RingedSpace.Hom.toRingCatSheafHom f`.
private theorem pullback_isQuasicoherent_onRingedSpaces
    (f : X ⟶ Y) (𝒢 : RingedSpace.Modules Y) [𝒢.IsQuasicoherent] :
    ((f^*).obj 𝒢).IsQuasicoherent :=
  SheafOfModules.RingedSite.pullback_isQuasicoherent.{u, u, u, u, u, u, u, u, u, u, u, u, u}
    (Opens.map f.hom.base) (RingedSpace.Hom.toRingCatSheafHom f) 𝒢

/-- Lemma 17.10.4: for a morphism of ringed spaces
`f : (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)`, the pullback of a quasi-coherent
`\mathcal{O}_Y`-module is quasi-coherent. -/
@[stacks 01BG]
theorem ringedSpaceModulePullback_isQuasicoherent
    (f : X ⟶ Y) (𝒢 : RingedSpace.Modules Y) [𝒢.IsQuasicoherent] :
    ((f^*).obj 𝒢).IsQuasicoherent :=
  by
    simpa using pullback_isQuasicoherent_onRingedSpaces f 𝒢

end AlgebraicGeometry
