import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Lemma_17_29_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X S : RingedSpace.{u}}
variable (f : X ⟶ S)
variable (ℱ 𝒢 : SheafOfModules.{u} (RingedSpace.ringCatSheaf X))
variable (k : ℕ)

/- Domain-style sampling for Definition 17.29.8:
- primary domain: relative differential operators between module sheaves on a morphism of ringed
  spaces;
- sampled owner declarations:
  `RingedSpace.Hom.inverseImageStructureSheafHomComm`,
  `RingedSpace.ringCatSheaf`,
  `IsDifferentialOperatorOfOrder`,
  `differentialOperatorsFunctor`,
  `Definition_17_28_10`'s ringed-space specialization pattern for `Ω[f]`;
- best owner abstraction: the Chapter 17 functor owner
  `(differentialOperatorsFunctor φ ℱ k).obj 𝒢`, specialized to the inverse-image structure-sheaf
  map `φ := RingedSpace.Hom.inverseImageStructureSheafHomComm f`;
- primitive data: only the ringed-space morphism `f`, the two `𝒪_X`-module sheaves `ℱ`, `𝒢`,
  and the order `k`;
- derived API: the subtype of morphisms together with the proof that they satisfy the relative
  order-`k` differential-operator condition.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization `Diff^k_{X/S}(ℱ, 𝒢)`;
- `core/canonical`: `(differentialOperatorsFunctor φ ℱ k).obj 𝒢`;
- `bridge/view`: specialization along
  `RingedSpace.Hom.inverseImageStructureSheafHomComm f`.

This numbered item only specializes the already-defined Chapter 17 owner to a morphism of ringed
spaces. The main entry should therefore be a direct canonical recall, not a parallel set-valued
wrapper. -/

/- Definition 17.29.8: for a morphism of ringed spaces `f : X ⟶ S`, the relative differential
operators `Diff^k_{X/S}(ℱ, 𝒢)` are the order-`k` differential operators from `ℱ` to `𝒢`
relative to the inverse-image structure-sheaf morphism
`RingedSpace.Hom.inverseImageStructureSheafHomComm f`. -/
#check
  (differentialOperatorsFunctor
    (RingedSpace.Hom.inverseImageStructureSheafHomComm f) ℱ k).obj 𝒢

end AlgebraicGeometry.RingedSpace
