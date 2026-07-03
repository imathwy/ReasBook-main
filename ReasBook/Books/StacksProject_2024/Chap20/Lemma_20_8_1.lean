import Mathlib
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap21.Lemma_21_12_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.8.1:
- primary domain: restriction maps on sections of an injective `\mathcal O_X`-module over nested
  opens of a ringed space;
- sampled owner declarations:
  `injective_module_restriction_surjective_of_mono`,
  `moduleSheafRestrictionToOpen`,
  `moduleSheafExtensionByZeroAdjunction`,
  `TopCat.Sheaf.IsFlasque`;
- best owner abstraction: the general site-level owner
  `injective_module_restriction_surjective_of_mono`, with the ringed-space restriction functor as
  the geometric specialization and flasqueness only as a later derived consequence;
- primitive data: an injective object `ℐ : (RingedSpace.Modules X)` and an inclusion `U' ≤ U`, equivalently
  the canonical monomorphism `homOfLE hU'U : U' ⟶ U`;
- derived API: surjectivity of the section restriction map `ℐ(U) → ℐ(U')`.

Source/core/bridge triage:
- `source-facing`: the explicit surjectivity statement on nested opens from the textbook;
- `core/canonical`: the project-level site theorem
  `injective_module_restriction_surjective_of_mono`;
- `bridge/view`: specialize that theorem to the site of opens of the ringed space and the mono
  `homOfLE hU'U`.

This file keeps the source-facing statement as the main public entry, but its proof should now be a
thin specialization of the canonical site-level owner rather than a parallel local argument. -/

variable {X : RingedSpace.{u}} {U' U : Opens X}

-- Proof sketch: this is the ringed-space specialization of the project's general site-level owner
-- `injective_module_restriction_surjective_of_mono`, applied to the canonical mono
-- `homOfLE hU'U : U' ⟶ U`.
/-- Lemma 20.8.1: if `\mathcal I` is an injective `\mathcal O_X`-module and `U' \subseteq U` are
open subsets of `X`, then the restriction map `\mathcal I(U) \to \mathcal I(U')` is surjective.
-/
theorem module_sections_restriction_surjective_of_injective
    (ℐ : (RingedSpace.Modules X)) (hℐ : Injective ℐ) (hU'U : U' ≤ U) :
    Function.Surjective (ℐ.val.map (homOfLE hU'U).op) :=
  injective_module_restriction_surjective_of_mono (homOfLE hU'U) ℐ hℐ

end AlgebraicGeometry.RingedSpace
