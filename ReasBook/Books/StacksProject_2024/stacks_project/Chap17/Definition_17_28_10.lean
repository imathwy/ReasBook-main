import Mathlib
import StacksProject_2024.stacks_project.Chap06.Lemma_6_26_4
import StacksProject_2024.stacks_project.Chap17.Definition_17_4_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_28_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace
open AlgebraicGeometry
open PresheafOfModules.DifferentialsConstruction
open TopCat.Sheaf
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X S : RingedSpace.{u}}

open RingedSpace.Hom

/- Domain-style sampling for Definition 17.28.10:
- primary domain: relative differentials of a morphism of commutative ringed spaces;
- sampled owner declarations:
  `inverseImageStructureSheafHomComm`,
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferential`,
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`;
- best owner abstraction: `TopCat.Sheaf.relativeDifferentials`, specialized along the inverse-image
  structure-sheaf morphism `inverseImageStructureSheafHomComm f` of a ringed-space map;
- primitive data in this file: no new primitive data beyond the canonical Chapter 6 inverse-image
  morphism `inverseImageStructureSheafHomComm f : f⁻¹ 𝒪_S ⟶ 𝒪_X`;
- derived API: only the source-facing ringed-space notation `Ω[f]`, `d[f]`; exact-interface
  theorem wrappers should be deleted in favor of direct reuse of the sheaf-level owner theorems.

Source/core/bridge triage:
- `source-facing`: the ringed-space notation `Ω[f]` for `Ω_{X/S}` and `d[f]` for the universal
  derivation attached to `f : X ⟶ S`;
- `core/canonical`: `TopCat.Sheaf.relativeDifferentials`;
- `bridge/view`: reuse of the existing Chapter 6 inverse-image morphism
  `inverseImageStructureSheafHomComm f`;
- this item therefore exposes the source-facing ringed-space surface on top of the sheaf owner
  and reuses the established bridge/view layer rather than redeclaring duplicate theorem wrappers.
  The relative derivation type already has the canonical Chapter 17 owner surface `Der[φ ; F]`. -/

scoped[AlgebraicGeometry] notation3:max "Ω[" f "]" =>
  Ω(inverseImageStructureSheafHomComm f)

scoped[AlgebraicGeometry] notation3:max "d[" f "]" =>
  relativeDifferential (inverseImageStructureSheafHomComm f)

end AlgebraicGeometry.RingedSpace
