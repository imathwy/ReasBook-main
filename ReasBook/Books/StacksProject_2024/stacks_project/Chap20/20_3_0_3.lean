import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap20.Bounded_below_derived_sections_at_open

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open Opposite
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)
variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyCategoryToDerivedBelow
    (SheafOfModules.evaluation X.ringCatSheaf (op U)))
  (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]

local notation "ModX" => RingedSpace.Modules X
local notation "ΓModU" => ModuleCat (sectionsRingOnOpen X U)

/- Domain-style sampling for 20.3.0.3:
- primary domain: bounded-below derived sections of `𝒪_X`-modules over an open subset of a
  ringed space;
- sampled owner declarations:
  `boundedBelowDerivedSectionsAtOpen`,
  `Functor.totalRightDerived`;
- best owner abstraction: the source-facing Chapter 20 owner
  `boundedBelowDerivedSectionsAtOpen U : D⁺(ModX) ⥤ D⁺(ΓModU)`, whose defining body is the
  canonical bounded-below specialization of `Functor.totalRightDerived`;
- primitive data: the ringed space `X`, the open subset `U`, and the canonical right-derived
  functor instance for sections on `U`;
- derived API: the bounded-below derived sections functor `RΓ(U, -)`.

Source/core/bridge triage:
- `source-facing`: `boundedBelowDerivedSectionsAtOpen U`, the Chapter 20 owner for the bounded-
  below derived sections functor `RΓ(U, -)`;
- `core/canonical`: the `Functor.totalRightDerived` specialization used in that owner;
- `bridge/view`: none. This item is a recall of the existing source-facing chapter owner rather
  than a new local specialization.
-/

/- Owner recall: the bounded-below derived sections functor on `U` is the Chapter 20 owner
`boundedBelowDerivedSectionsAtOpen U`. -/
recall boundedBelowDerivedSectionsAtOpen

/- 20.3.0.3: for a ringed space `X` and an open subset `U ⊆ X`, the bounded-below derived
sections functor `RΓ(U, -)` is the Chapter 20 owner
`boundedBelowDerivedSectionsAtOpen U : D⁺(ModX) ⥤ D⁺(ΓModU)`. -/
#check (boundedBelowDerivedSectionsAtOpen U : D⁺(ModX) ⥤ D⁺(ΓModU))

end

end AlgebraicGeometry.RingedSpace
