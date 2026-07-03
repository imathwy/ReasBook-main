import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open SheafOfModules.RingedSite

namespace SectionNonvanishingOpen

/- Lean parses bare `X_[s]` as indexed access, so the reusable owner-level notation is
parenthesized: `(X)_[s]`. In a local context with a fixed ambient variable `X`, one can then add
`local notation "X_[" s "]" => (X)_[s]` to recover the exact textbook surface. -/
set_option quotPrecheck false in
scoped macro:1075 X:term noWs "_[" s:term noWs "]" : term => do
  let sectionNonvanishingOpen :=
    Lean.mkIdent `AlgebraicGeometry.RingedSpace.sectionNonvanishingOpen
  `($sectionNonvanishingOpen $X _ $s)

end SectionNonvanishingOpen

open scoped SectionNonvanishingOpen

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})

local notation "ModX" => RingedSpace.Modules X
local notation "IsInvertible" =>
  @SheafOfModules.RingedSite.IsInvertible _ _ (Opens.grothendieckTopology X) X.sheaf _ _

/- Domain-style sampling for Lemma 17.25.10:
- primary domain: nonvanishing loci of global sections of invertible `\mathcal O_X`-modules on a
  ringed space;
- inspected owner declarations:
  `RingedSpace.stalkModuleCat`,
  `SheafOfModules.over`,
  `SheafOfModules.unitHomEquiv`,
  `SheafOfModules.pushforwardSections`,
  `SheafOfModules.RingedSite.IsInvertible`;
- best owner abstraction: the source-facing owners are the nonvanishing locus/open of a section,
  while the core canonical layer is the invertibility owner `IsInvertible` together with the
  bundled stalk owner `RingedSpace.stalkModuleCat`; the restricted section map
  `\mathcal O_U \to \mathcal L|_U` is bridge/view data built from the unit/sections adjunction on
  `ℒ.over U`;
- primitive data: a module `ℒ : ModX` and a global section `s : ℒ.sections`;
- derived API: openness of the nonvanishing locus, the associated open subset `(X)_[s]`, and the
  restricted section morphism on that open.

Source/core/bridge triage:
- `source-facing`: `sectionNonvanishingLocus` and `sectionNonvanishingOpen`;
- `core/canonical`: `IsInvertible`, `RingedSpace.stalkModuleCat`, `SheafOfModules.over`, and
  `SheafOfModules.unitHomEquiv`;
- `bridge/view`: `sectionOverHom` and its specialization to `sectionNonvanishingOpen`.
-/

/-- The morphism `\mathcal O_U \to \mathcal L|_U` induced by restricting a global section of
`\mathcal L` to an open subset `U`. -/
noncomputable abbrev sectionOverHom (ℒ : ModX) (s : ℒ.sections) (U : Opens X) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ ℒ.over U :=
  (ℒ.over U).unitHomEquiv.symm
    (SheafOfModules.pushforwardSections (𝟙 (X.ringCatSheaf.over U)) s)

section Nonvanishing

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- The source-defined nonvanishing locus of a section of an `\mathcal O_X`-module. -/
def sectionNonvanishingLocus (ℒ : ModX) (s : ℒ.sections) : Set X :=
  {x | (TopCat.Presheaf.Γgerm ℒ.val.presheaf x (s.1 (op ⊤))) ∉
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
      (⊤ : Submodule (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℒ x)))}

-- Proof sketch: for a point where the stalk germ of `s` is not in
-- `\mathfrak m_x \mathcal L_x`, invertibility identifies `\mathcal L_x` with a free rank-one
-- module over the local ring `\mathcal O_{X,x}`; Nakayama then shows that the germ of `s`
-- generates `\mathcal L_x`. Choosing local dual sections with evaluation `1` gives an open
-- neighbourhood basis inside the locus, hence the locus is open.
section Invertible

variable [monoidalModX : MonoidalCategory ModX]

local instance ringedSiteMonoidalCategory :
    MonoidalCategory (ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf) := by
  simpa using monoidalModX

/-- Lemma 17.25.10: for an invertible `\mathcal O_X`-module `\mathcal L` and a global section
`s`, the set of points where the germ of `s` is not contained in
`\mathfrak m_x \mathcal L_x` is open. -/
theorem sectionNonvanishingLocus_isOpen (ℒ : ModX)
    [IsInvertible ℒ]
    (s : ℒ.sections) :
    IsOpen (sectionNonvanishingLocus X ℒ s) := sorry

/-- The open subset cut out by the nonvanishing locus of a section of an invertible
`\mathcal O_X`-module. -/
def sectionNonvanishingOpen (ℒ : ModX)
    [IsInvertible ℒ]
    (s : ℒ.sections) : Opens X :=
  ⟨sectionNonvanishingLocus X ℒ s, sectionNonvanishingLocus_isOpen X ℒ s⟩

-- Proof sketch: on the open locus from the previous theorem, each stalk germ of `s` is a basis
-- vector of the rank-one free stalk `\mathcal L_x`. A morphism of sheaves of modules is an
-- isomorphism iff it is an isomorphism on all stalks, so the restricted map
-- `\mathcal O_{(X)_[s]} \to \mathcal L|_{(X)_[s]}` induced by `s` is an isomorphism.
/-- On the nonvanishing open `(X)_[s]`, the restricted section induces an isomorphism
`\mathcal O_{(X)_[s]} \cong \mathcal L|_{(X)_[s]}`. -/
instance isIso_sectionOverHom_sectionNonvanishingOpen (ℒ : ModX)
    [IsInvertible ℒ]
    (s : ℒ.sections) :
    IsIso (sectionOverHom X ℒ s ((X)_[s])) := sorry
end Invertible

end Nonvanishing

end AlgebraicGeometry.RingedSpace
