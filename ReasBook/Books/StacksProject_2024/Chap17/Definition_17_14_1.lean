import Mathlib
import StacksProject_2024.Chap17.Definition_17_5_1

open TopologicalSpace
open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

private abbrev FreeOn (U : Opens X) (I : Type u) :
    SheafOfModules (X.ringCatSheaf.over U) :=
  SheafOfModules.free.{u} I

/- Domain-style sampling for Definition 17.14.1:
- primary domain: locally free sheaves of modules on ringed spaces;
- inspected owner declarations:
  `Module.LocallyFree`,
  `Module.FiniteLocallyFree`,
  `Module.FiniteLocallyFreeOfRank`,
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`;
- best owner abstraction: the ringed-space module owner `(RingedSpace.Modules X)`, together with the
  localized restriction owner `ℱ.over U` and the canonical free and unit sheaves over
  `(RingedSpace.ringCatSheaf X)`;
- primitive data: local trivializations of `ℱ.over U` by free sheaves, with finiteness or fixed
  rank carried only by the local basis type;
- derived API: freeness implies local freeness, finite local freeness implies local freeness,
  constant rank implies finite local freeness, and the structure sheaf has rank `1`.

Source/core/bridge triage:
- `source-facing`: the Stacks Project definitions of locally free, finite locally free, and
  finite locally free of constant rank on a ringed space;
- `core/canonical`: the ambient owner category `(RingedSpace.Modules X)`;
- `bridge/view`: the derived instances and theorem below, which keep the owner abstraction and
  avoid parallel wrapper data. -/

/-- Definition 17.14.1 (1): an `\mathcal O_X`-module sheaf is locally free if every point has an
open neighbourhood on which the restricted sheaf is free. -/
class IsLocallyFree (ℱ : X.Modules) : Prop where
  /-- Around every point, the sheaf becomes isomorphic to a free module sheaf on some open
  neighbourhood. -/
  exists_open_neighborhood_iso_free (x : X) :
      ∃ (U : Opens X) (_ : x ∈ U) (I : Type u),
      Nonempty (ℱ.over U ≅ FreeOn U I)

/-- Definition 17.14.1 (2): an `\mathcal O_X`-module sheaf is finite locally free if every point
has an open neighbourhood on which the restricted sheaf is free on a finite index set. -/
class IsFiniteLocallyFree (ℱ : X.Modules) : Prop where
  /-- Around every point, the sheaf becomes isomorphic to a finite free module sheaf on some open
  neighbourhood. -/
  exists_open_neighborhood_iso_free (x : X) :
      ∃ (U : Opens X) (_ : x ∈ U) (I : Type u), Finite I ∧
        Nonempty (ℱ.over U ≅ FreeOn U I)

/-- An `\mathcal O_X`-module sheaf is locally a direct summand of a finite free module if every
point has an open neighbourhood on which the restricted sheaf is a retract of a finite free
module sheaf. -/
class IsLocallyDirectSummandOfFiniteFree (ℱ : X.Modules) : Prop where
  /-- Around every point, the sheaf becomes a retract of a finite free module sheaf on some open
  neighbourhood. -/
  exists_open_neighborhood_retract_free (x : X) :
      ∃ (U : Opens X) (_ : x ∈ U) (I : Type u), Finite I ∧
        Nonempty (Retract (ℱ.over U) (FreeOn U I))

/-- Definition 17.14.1 (3): an `\mathcal O_X`-module sheaf is finite locally free of rank `r` if
every point has an open neighbourhood on which the restricted sheaf is isomorphic to
`\mathcal O_U^{\oplus r}`. -/
class IsFiniteLocallyFreeOfRank (r : ℕ) (ℱ : X.Modules) : Prop where
  /-- Around every point, the sheaf becomes isomorphic to the free rank-`r` module sheaf on some
  open neighbourhood. -/
  exists_open_neighborhood_iso_free (x : X) :
      ∃ (U : Opens X) (_ : x ∈ U),
        Nonempty (ℱ.over U ≅ FreeOn U (ULift.{u} (Fin r)))

-- Proof sketch: use the whole space `X` as the neighbourhood of each point; the restriction of a
-- free sheaf to any open remains free on the same basis.
/-- A free `\mathcal O_X`-module sheaf is locally free. -/
instance free_isLocallyFree
    (ι : Type u) :
    IsLocallyFree (SheafOfModules.free.{u} ι : X.Modules) :=
  sorry

-- Proof sketch: forget the finiteness data in each local finite free trivialization and keep the
-- same open neighbourhoods and free local models.
/-- A finite locally free sheaf is locally free. -/
instance isFiniteLocallyFree_to_isLocallyFree
    (ℱ : X.Modules) [ℱ.IsFiniteLocallyFree] :
    ℱ.IsLocallyFree := sorry

-- Proof sketch: each local isomorphism with a finite free module exhibits the sheaf as a retract
-- of that finite free module via the inverse isomorphism.
/-- A finite locally free sheaf is locally a direct summand of a finite free sheaf. -/
instance isFiniteLocallyFree_to_isLocallyDirectSummandOfFiniteFree
    (ℱ : X.Modules) [ℱ.IsFiniteLocallyFree] :
    ℱ.IsLocallyDirectSummandOfFiniteFree := by
  classical
  refine ⟨?_⟩
  intro x
  rcases (inferInstance : IsFiniteLocallyFree ℱ).exists_open_neighborhood_iso_free x with
    ⟨U, hxU, I, hI, hIso⟩
  rcases hIso with ⟨e⟩
  exact ⟨U, hxU, I, hI, ⟨e.retract⟩⟩

-- Proof sketch: a local isomorphism with `\mathcal O_U^{\oplus r}` is in particular a local
-- isomorphism with a finite free module sheaf, since `Fin r` is finite.
/-- A finite locally free sheaf of rank `r` is finite locally free. -/
theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank (r : ℕ)
    (ℱ : X.Modules) [IsFiniteLocallyFreeOfRank r ℱ] :
    IsFiniteLocallyFree ℱ := sorry

-- Proof sketch: for each point, take the whole space `X` as the neighbourhood; the structure
-- sheaf is already the free rank-one module sheaf over itself.
/-- The structure sheaf of a ringed space is finite locally free of rank `1`. -/
instance (X : RingedSpace.{u}) :
    IsFiniteLocallyFreeOfRank 1 (SheafOfModules.unit X.ringCatSheaf : X.Modules) := sorry

/-- The structure sheaf of a ringed space is finite locally free. -/
instance (X : RingedSpace.{u}) :
    IsFiniteLocallyFree (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank 1
    (SheafOfModules.unit X.ringCatSheaf)

end SheafOfModules
