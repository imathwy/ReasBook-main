import Mathlib
import stacks_proof.stacks_project.Chap17.Lemma_17_30_3
import stacks_proof.stacks_project.Chap17.Definition_17_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry
open TopCat.Sheaf
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

/- Domain-style sampling for Lemma 17.30.5:
- primary domain: relative de Rham differentials on a morphism of ringed spaces;
- sampled owner declarations:
  `RingedSpace.Hom.inverseImageStructureSheafHomComm`,
  `ringSheafMap`,
  `TopCat.Sheaf.deRhamComplex`,
  `TopCat.Sheaf.deRhamDifferential_isDifferentialOperatorOfOrder`,
  `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`;
- best owner abstraction: the sheaf-level owner theorem
  `TopCat.Sheaf.deRhamDifferential_isDifferentialOperatorOfOrder`, specialized along
  `RingedSpace.Hom.inverseImageStructureSheafHomComm f`, with the ringed-space notation
  `Ω^•[f]` used only as a thin bridge;
- primitive data here: only the morphism `f : X ⟶ Y` and the degree `i`;
- derived API: the order-one differential-operator statement for the degree-`i` owner
  differential.

Source/core/bridge triage:
- `source-facing`: the order-one differential-operator statement for the relative de Rham
  differential;
- `core/canonical`: `TopCat.Sheaf.deRhamComplex` and
  `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`;
- `bridge/view`: the ringed-space notation `Ω^•[f]`.

This item is therefore a direct bridge/view recall: the ringed-space statement is exactly the
sheaf-level owner theorem specialized along `RingedSpace.Hom.inverseImageStructureSheafHomComm f`,
so the file should reuse that owner directly rather than introduce a parallel theorem wrapper. -/

variable (f : X ⟶ Y) (i : ℕ)

/- Lemma 17.30.5: for a morphism of ringed spaces `f : X ⟶ Y`, each differential
`d : \Omega^i_{X/Y} \to \Omega^{i + 1}_{X/Y}` in the relative de Rham complex is a differential
operator of order `1` on `X/Y`. This is the sheaf-level owner theorem of Lemma `17.30.3`,
specialized to the inverse-image structure-sheaf morphism of `f`. -/
#check
  TopCat.Sheaf.deRhamDifferential_isDifferentialOperatorOfOrder
    (RingedSpace.Hom.inverseImageStructureSheafHomComm f) i

end AlgebraicGeometry.RingedSpace
