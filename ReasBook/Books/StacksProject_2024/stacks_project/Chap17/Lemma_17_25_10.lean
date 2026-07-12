import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_25_1
import StacksProject_2024.Chap17.Lemma_17_25_4
import StacksProject_2024.Chap17.SectionNonvanishingLocus

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

namespace SectionNonvanishingOpen

/- Lean parses bare `X_[s]` as indexed access, so the reusable owner-level notation is
parenthesized: `(X)_[s]`. -/
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
/- Domain-style sampling for Lemma 17.25.10:
- primary domain: nonvanishing loci of global sections of invertible `\mathcal O_X`-modules;
- public API: the morphism induced by a restricted global section, openness of the nonvanishing
  locus, the associated open subset `(X)_[s]`, and the isomorphism on that open.

This is an upstream statement dependency.  The previous proof attempted to use several unavailable
pullback-stalk and unit-chart helpers.  Keep the public API and leave the proof obligations explicit
so downstream chapters can build their imports. -/

/-- The morphism `\mathcal O_U 	o \mathcal L|_U` induced by restricting a global section of
`\mathcal L` to an open subset `U`. -/
noncomputable abbrev sectionOverHom (ℒ : ModX) (s : ℒ.sections) (U : Opens X) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ ℒ.over U :=
  (ℒ.over U).unitHomEquiv.symm
    (SheafOfModules.pushforwardSections (𝟙 (X.ringCatSheaf.over U)) s)

section Nonvanishing

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- Lemma 17.25.10: for an invertible `\mathcal O_X`-module `\mathcal L` and a global section
`s`, the set of points where the germ of `s` is not contained in
`\mathfrak m_x \mathcal L_x` is open. -/
theorem sectionNonvanishingLocus_isOpen (ℒ : ModX)
    [MonoidalCategory ModX]
    [Functor.IsEquivalence (CategoryTheory.MonoidalCategory.tensorRight ℒ)]
    (s : ℒ.sections) :
    IsOpen (sectionNonvanishingLocus X ℒ s) := by
  sorry

/-- The open subset cut out by the nonvanishing locus of a section of an invertible
`\mathcal O_X`-module. -/
def sectionNonvanishingOpen (ℒ : ModX)
    [MonoidalCategory ModX]
    [Functor.IsEquivalence (CategoryTheory.MonoidalCategory.tensorRight ℒ)]
    (s : ℒ.sections) : Opens X :=
  ⟨sectionNonvanishingLocus X ℒ s, sectionNonvanishingLocus_isOpen X ℒ s⟩

/-- On the nonvanishing open `(X)_[s]`, the restricted section induces an isomorphism
`\mathcal O_{(X)_[s]} \cong \mathcal L|_{(X)_[s]}`. -/
instance isIso_restrictedSection_sectionNonvanishingOpen (ℒ : ModX)
    [MonoidalCategory ModX]
    [Functor.IsEquivalence (CategoryTheory.MonoidalCategory.tensorRight ℒ)]
    (s : ℒ.sections) :
    IsIso (sectionOverHom X ℒ s ((X)_[s])) := by
  sorry

end Nonvanishing

end AlgebraicGeometry.RingedSpace
