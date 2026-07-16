import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_14_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_25_1
import StacksProject_2024.stacks_project.Chap18.Definition_18_40_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open AlgebraicGeometry
open SheafOfModules.RingedSite
open TopologicalSpace
open scoped SheafOfModules.RingedSite

noncomputable section

namespace AlgebraicGeometry.RingedSpace

universe u

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦
    Functor.IsEquivalence (CategoryTheory.MonoidalCategory.tensorRight ℒ))

/- Domain-style sampling for Lemma 17.25.4:
- primary domain: invertible `\mathcal O_X`-modules and finite locally free rank-one modules on a
  ringed space;
- source-facing public API: local-unit dichotomy from local stalk rings, rank-one finite locally
  free modules are invertible, and invertible modules are locally free of rank one when stalks are
  local rings.

This file is an upstream statement dependency.  The previous version attempted to prove the bridge
through several private slice/restriction and stalk-tensor helpers that currently do not compile in
this Lake state.  Keep the public source statements available and leave the proof obligations
explicit. -/

/-- If all stalks of a ringed space are local rings, then the opens site satisfies the local-unit
dichotomy. -/
theorem hasLocalUnitDichotomy_of_stalk_isLocalRing
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    HasLocalUnitDichotomy (Opens.grothendieckTopology X) X.sheaf := by
  sorry

variable [MonoidalCategory (RingedSpace.Modules X)]

/-- Lemma 17.25.4 (1): a finite locally free `\mathcal O_X`-module of rank `1` on a ringed space
is invertible. -/
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one
    (ℒ : ModX) [SheafOfModules.IsFiniteLocallyFreeOfRank 1 ℒ] :
    IsInvertibleX ℒ := by
  sorry

/-- Lemma 17.25.4 (2): if every stalk `\mathcal O_{X, x}` is a local ring, then every invertible
`\mathcal O_X`-module is locally free of rank `1`. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible_of_stalk_isLocalRing
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x))
    (ℒ : ModX) [IsInvertibleX ℒ] :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 ℒ := by
  sorry

end AlgebraicGeometry.RingedSpace
