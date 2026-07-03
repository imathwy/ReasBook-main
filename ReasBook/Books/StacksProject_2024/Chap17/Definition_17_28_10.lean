import Mathlib
import stacks_project.Chap06.Lemma_6_26_4
import stacks_project.Chap17.Definition_17_4_1
import stacks_project.Chap17.Definition_17_28_3

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

/- Domain-style sampling for Definition 17.28.10:
- primary domain: relative differentials of a morphism of commutative ringed spaces;
- sampled owner declarations:
  `RingedSpace.Hom.inverseImageStructureSheafHomComm`,
  `AlgebraicGeometry.ringedSpaceRingCatSheaf`,
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferential`,
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`,
  `PresheafOfModules.sheafification`;
- best owner abstraction: `TopCat.Sheaf.relativeDifferentials`, specialized along the inverse-image
  structure-sheaf morphism `RingedSpace.Hom.inverseImageStructureSheafHomComm f` of a ringed-space
  map;
- primitive data in this file: no new primitive data beyond the canonical Chapter 6 inverse-image
  morphism `RingedSpace.Hom.inverseImageStructureSheafHomComm f : f⁻¹ 𝒪_S ⟶ 𝒪_X`;
- derived API: the source-facing notation `Ω[f]`, `d[f]`, together with the specialized
  definitional and representing theorems below.

Source/core/bridge triage:
- `source-facing`: the ringed-space notation `Ω[f]` for `Ω_{X/S}` and `d[f]` for the universal
  derivation attached to `f : X ⟶ S`;
- `core/canonical`: `TopCat.Sheaf.relativeDifferentials`;
- `bridge/view`: reuse of the existing Chapter 6 inverse-image morphism
  `RingedSpace.Hom.inverseImageStructureSheafHomComm f`;
- this item therefore exposes the source-facing ringed-space surface on top of the sheaf owner
  and reuses the established bridge/view layer rather than redeclaring a second public owner.
  The relative derivation type already has the canonical Chapter 17 owner surface `Der[φ ; F]`,
  so this file should use that directly instead of introducing a second ringed-space alias. -/

scoped[AlgebraicGeometry] notation3:max "Ω[" f "]" =>
  relativeDifferentials (RingedSpace.Hom.inverseImageStructureSheafHomComm f)

/-- The sheaf of differentials is the sheafification of the presheaf of relative differentials. -/
theorem differentials_def (f : X ⟶ S) :
    Ω[f] =
      (PresheafOfModules.sheafification (𝟙 (RingedSpace.ringCatSheaf X).obj)).obj
        (relativeDifferentials'
          (RingedSpace.Hom.inverseImageStructureSheafHomComm f).hom) :=
  rfl

scoped[AlgebraicGeometry] notation3:max "d[" f "]" =>
  relativeDifferential (RingedSpace.Hom.inverseImageStructureSheafHomComm f)

/-- The sheaf of differentials represents derivations out of `𝒪_X` relative to `S`. -/
theorem differentials_representsDerivations
    (f : X ⟶ S) (F : SheafOfModules.{u} (RingedSpace.ringCatSheaf X))
    (D : Der[RingedSpace.Hom.inverseImageStructureSheafHomComm f ; F]) :
    ∃! α : Ω[f] ⟶ F,
      RelativeDerivation.postcomp (d[f]) α = D := by
  simpa using
    (relativeDifferentials_representsDerivations
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f) F D)

end AlgebraicGeometry.RingedSpace
