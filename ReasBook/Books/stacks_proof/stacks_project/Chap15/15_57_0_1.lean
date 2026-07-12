import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.Chap13.Proposition_13_16_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable (M : ModuleCat R)

local notation "QisMinus" => boundedAboveHomotopyQuasiIso (ModuleCat R)
local notation "KminusToDminus" =>
  mapBoundedAboveHomotopyCategoryToDerivedAbove (tensorRight M)

attribute [local instance] mapBoundedAboveHomotopyToDerivedAbove_isLocalization

/- Domain-style sampling for 15.57.0.1:
- primary domain: bounded-above left derived functors on homotopy and derived categories of
  `R`-modules;
- sampled owner declarations:
  `Functor.totalLeftDerived`,
  `mapBoundedAboveHomotopyCategoryToDerivedAbove`,
  `mapBoundedAboveHomotopyToDerivedAbove_isLocalization`,
  `boundedAbove_hasLeftDerivedFunctor_of_epi_from_boundedAboveLeftAcyclic`;
- best owner abstraction: the canonical owner is `Functor.totalLeftDerived`, specialized to the
  bounded-above tensor functor `KminusToDminus` along the bounded-above localization bridge
  `mapBoundedAboveHomotopyToDerivedAbove`;
- primitive data: the underived bounded-above tensor functor `KminusToDminus` and the existence
  witness for its left derived functor; the localization witness for
  `mapBoundedAboveHomotopyToDerivedAbove` is the Chapter 13 owner theorem
  `mapBoundedAboveHomotopyToDerivedAbove_isLocalization`;
- source/core/bridge triage:
  `source-facing`: the bounded-above derived tensor functor with fixed right factor `M`;
  `core/canonical`: `Functor.totalLeftDerived`;
  `bridge/view`: the bounded-above localization functor
    `mapBoundedAboveHomotopyToDerivedAbove`.
-/

-- Proof sketch: every bounded-above complex of `R`-modules admits a bounded-above projective
-- resolution. Projective modules compute tensoring with the fixed module `M`, so they supply an
-- epi-cover by bounded-above left-acyclic objects; the Chapter 13 owner theorem
-- `boundedAbove_hasLeftDerivedFunctor_of_epi_from_boundedAboveLeftAcyclic` then gives the
-- existence statement directly.
/-- The object property of bounded-above left-acyclic modules for tensoring with a fixed right
factor `M` admits epi covers. -/
local instance tensorRight_boundedAboveLeftAcyclic_hasEpiCover :
    ObjectProperty.HasEpiCover
      (IsBoundedAboveLeftAcyclicForAdditiveFunctor (tensorRight M)) := by
  sorry

/-- Tensoring on the right with a fixed `R`-module admits a bounded-above left derived functor
`K^-(R) ⟶ D^-(R)`. -/
local instance tensorRight_boundedAbove_hasLeftDerivedFunctor :
    Functor.HasLeftDerivedFunctor KminusToDminus QisMinus :=
  boundedAbove_hasLeftDerivedFunctor_of_epi_from_boundedAboveLeftAcyclic (tensorRight M)

/- 15.57.0.1: for a fixed `R`-module `M`, the bounded-above derived tensor functor
`- \otimes_R^{\mathbf L} M` is the canonical total left derived functor of bounded-above
tensoring with `M` along `K^-(R) ⟶ D^-(R)`. -/
#check
  (Functor.totalLeftDerived KminusToDminus mapBoundedAboveHomotopyToDerivedAbove QisMinus :
    boundedAboveDerivedCategory (ModuleCat R) ⥤
      boundedAboveDerivedCategory (ModuleCat R))

end

end CategoryTheory
