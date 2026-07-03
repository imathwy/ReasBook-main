import Mathlib
import StacksProject_2024.Chap17.Lemma_17_17_2
import StacksProject_2024.Chap17.Lemma_17_18_2

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.18.3:
- primary domain: flat sheaves of modules of finite presentation on a ringed space, with local
  finite-free retracts as the canonical output;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.IsLocallyDirectSummandOfFiniteFree`,
  `CategoryTheory.Retract`;
- best owner abstraction: `SheafOfModules.IsLocallyDirectSummandOfFiniteFree` is the chapter-level
  owner for the local retract condition, while explicit maps `ι` and `π` are derived local data;
- primitive data: a sheaf `ℱ : (RingedSpace.Modules X)` together with flatness and finite presentation;
- derived API: the pointwise neighborhood statement extracted from the owner class via
  `exists_open_neighborhood_retract_free`.

Source/core/bridge triage:
- `source-facing`: the neighborhood-wise direct-summand formulation around a chosen point;
- `core/canonical`: `SheafOfModules.IsLocallyDirectSummandOfFiniteFree`;
- `bridge/view`: the companion theorem below unpacking a local `Retract` into maps `ι` and `π`.

This file should therefore make the owner theorem primary and derive the pointwise textbook shape
from it, rather than keeping the raw split-morphism data as the only public API.
-/

-- Proof sketch: choose finite local presentations and use Lemma `17.17.11` to kill the relation
-- map after shrinking. The resulting surjection from a finite free sheaf splits, so the local
-- restriction is a retract of a finite free sheaf.
/-- Lemma 17.18.3: a flat `\mathcal O_X`-module of finite presentation on a ringed space is
locally a direct summand of a finite free `\mathcal O_X`-module. -/
theorem isLocallyDirectSummandOfFiniteFree_of_isFinitePresentation_of_flat
    {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X))
    [ℱ.IsFinitePresentation] [SheafOfModules.RingedSite.IsFlat X.sheaf ℱ] :
    ℱ.IsLocallyDirectSummandOfFiniteFree := sorry

-- Proof sketch: apply the owner theorem to get a local retract `Retract (ℱ.over U) (free I)` and
-- then unpack its canonical inclusion and retraction maps.
/-- Lemma 17.18.3: if `\mathcal F` is a flat `\mathcal O_X`-module of finite presentation on a
ringed space `(X, \mathcal O_X)`, then around any point `x : X` there is an open neighbourhood
`U` such that `\mathcal F|_U` is a direct summand of a finite free `\mathcal O_U`-module. -/
theorem exists_open_neighborhood_direct_summand_of_finite_free_of_isFinitePresentation_of_flat
    {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X))
    [ℱ.IsFinitePresentation] [SheafOfModules.RingedSite.IsFlat X.sheaf ℱ] (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (I : Type u) (_ : Finite I)
      (ι : ℱ.over U ⟶ SheafOfModules.free.{u} I)
      (π : SheafOfModules.free.{u} I ⟶ ℱ.over U),
        ι ≫ π = 𝟙 (ℱ.over U) := by
  letI : ℱ.IsLocallyDirectSummandOfFiniteFree :=
    isLocallyDirectSummandOfFiniteFree_of_isFinitePresentation_of_flat ℱ
  rcases
      (inferInstance : ℱ.IsLocallyDirectSummandOfFiniteFree).exists_open_neighborhood_retract_free
        x with
    ⟨U, hxU, I, hI, hretract⟩
  rcases hretract with ⟨R⟩
  exact ⟨U, hxU, I, hI, R.i, R.r, R.retract⟩

end AlgebraicGeometry.RingedSpace
