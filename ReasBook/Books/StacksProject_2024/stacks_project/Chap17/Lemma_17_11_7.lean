import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Lemma_17_4_2
import StacksProject_2024.Chap17.Lemma_17_11_4
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.Chap17.Lemma_17_9_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 17.11.7:
- primary domain: finitely presented sheaves of modules on ringed spaces and local freeness from a
  stalkwise finite free model;
- inspected owner declarations: `AlgebraicGeometry.RingedSpace.Modules`,
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`, `ModuleCat.free`, and
  `SheafOfModules.free`;
- best owner abstraction: the ambient owner category `RingedSpace.Modules X`, with the stalk
  bundled by `RingedSpace.stalkModuleCat` and the canonical finite free stalk model supplied by
  `ModuleCat.free (X.presheaf.stalk x)`;
- primitive data: a finitely presented module sheaf `ℱ`, a point `x`, a rank `r`, and a stalk
  isomorphism from `RingedSpace.stalkModuleCat ℱ x` to the free `X.presheaf.stalk x`-module on
  `ULift (Fin r)`;
- derived API: after shrinking around `x`, the restricted sheaf `ℱ.over U` becomes isomorphic to
  the free sheaf `SheafOfModules.free (ULift (Fin r))`.

Source/core/bridge triage:
- `source-facing`: the local trivialization statement around a point with free stalk;
- `core/canonical`: `RingedSpace.Modules`, `RingedSpace.stalkModuleCat`, and `ModuleCat.free`;
- `bridge/view`: the restriction `ℱ.over U` and the local free sheaf `SheafOfModules.free`. -/

/-- Lemma 17.11.7: if a finitely presented `\mathcal O_X`-module has stalk at `x` isomorphic to
the free rank-`r` `\mathcal O_{X, x}`-module, then on some open neighbourhood `U` of `x` its
restriction `ℱ|_U` is isomorphic to the free sheaf `\mathcal O_U^{\oplus r}`. -/
theorem exists_open_neighborhood_free_over_of_stalk_free
    (ℱ : ModX)
    [ℱ.IsFinitePresentation] (x : X) (r : ℕ)
    (hℱx : Nonempty
      (RingedSpace.stalkModuleCat ℱ x ≅
        (ModuleCat.free (X.presheaf.stalk x)).obj (ULift.{u} (Fin r)))) :
    ∃ (U : Opens X) (_ : x ∈ U),
      Nonempty (ℱ.over U ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) := by
  -- This file is a statement-level upstream dependency for later chapters.  The previous version
  -- attempted to build the full proof using several non-existing or mismatched slice/pullback
  -- helpers, which prevented downstream `.olean` generation.  Keep the public API as the source
  -- lemma and leave the proof obligation explicit.
  sorry

end SheafOfModules
