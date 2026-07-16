import Mathlib
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap17.Lemma_17_29_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open SheafOfModules.RingedSite
open RingedSpace.Hom
open scoped AlgebraicGeometry

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
  `Definition_17_28_10`'s ringed-space specialization pattern for `Ω[f]`,
  `Remark_10_150_9`'s algebraic notation `Diff_{S⁄R}(M)`,
  `RingedSpace.Hom.inverseImageStructureSheafHomComm`,
  `SheafOfModules.RingedSite.differentialOperatorsFunctor`,
- best owner abstraction: the chapter-local differential-operator functor owner in the
  `SheafOfModules.RingedSite` namespace, specialized to the inverse-image structure-sheaf map
  `φ := inverseImageStructureSheafHomComm f`, with only a source-facing ringed-space notation
  layer on top;
- primitive data: only the ringed-space morphism `f`, the two `𝒪_X`-module sheaves `ℱ`, `𝒢`,
  and the order `k`;
- derived API: the subtype of morphisms together with the proof that they satisfy the relative
  order-`k` differential-operator condition, exposed on the source-facing surface as
  `Diff(f ; k ; ℱ, 𝒢)`.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization `Diff^k_{X/S}(ℱ, 𝒢)`, written in Lean as
  `Diff(f ; k ; ℱ, 𝒢)`;
- `core/canonical`:
  `(SheafOfModules.RingedSite.differentialOperatorsFunctor φ ℱ k).obj 𝒢`;
- `bridge/view`: specialization along `inverseImageStructureSheafHomComm f`.

This numbered item only specializes the already-defined Chapter 17 differential-operator owner to
a morphism of ringed spaces. The public owner should therefore stay that canonical functor value,
with only the source-facing ringed-space notation layer added on top. -/

/-- Definition 17.29.8: for a morphism of ringed spaces `f : X ⟶ S`, the relative differential
operators `Diff^k_{X/S}(ℱ, 𝒢)` are the order-`k` differential operators from `ℱ` to `𝒢`
relative to the inverse-image structure-sheaf morphism `inverseImageStructureSheafHomComm f`. -/
@[stacks 0G3X]
abbrev relativeDifferentialOperators :
    Type _ :=
  (differentialOperatorsFunctor (inverseImageStructureSheafHomComm f) ℱ k).obj 𝒢

scoped[AlgebraicGeometry] notation3:max "Diff(" f " ; " k " ; " ℱ ", " 𝒢 ")" =>
  (differentialOperatorsFunctor (inverseImageStructureSheafHomComm f) ℱ k).obj 𝒢

/-- Helper for Definition 17.29.8: the ringed-space notation `Diff(f ; k ; ℱ, 𝒢)` is exactly the
canonical Chapter 17 differential-operator object specialized along
`inverseImageStructureSheafHomComm f`. -/
@[simp] theorem diff_eq_differentialOperatorsFunctor_obj :
    Diff(f ; k ; ℱ, 𝒢) =
      (differentialOperatorsFunctor (inverseImageStructureSheafHomComm f) ℱ k).obj 𝒢 := by
  -- The source-facing notation is defined by this specialization, so the equality is definitional.
  rfl

/-- Helper for Definition 17.29.8: an element of `Diff(f ; k ; ℱ, 𝒢)` is, by construction, an
order-`k` differential operator relative to `inverseImageStructureSheafHomComm f`. -/
@[simp] theorem diff_isDifferentialOperatorOfOrder
    (D : Diff(f ; k ; ℱ, 𝒢)) :
    TopCat.Sheaf.IsDifferentialOperatorOfOrder (inverseImageStructureSheafHomComm f) D.1 k := by
  -- Unpacking the subtype witness in `Diff(f ; k ; ℱ, 𝒢)` gives exactly the defining property.
  exact D.2

/-- Helper for Definition 17.29.8: a morphism together with its relative order-`k` witness
packages into an element of `Diff(f ; k ; ℱ, 𝒢)`. -/
abbrev diff_of_isDifferentialOperatorOfOrder
    (D : (restrictionAlong (inverseImageStructureSheafHomComm f)).obj ℱ ⟶
      (restrictionAlong (inverseImageStructureSheafHomComm f)).obj 𝒢)
    (hD : TopCat.Sheaf.IsDifferentialOperatorOfOrder (inverseImageStructureSheafHomComm f) D k) :
    Diff(f ; k ; ℱ, 𝒢) :=
  ⟨D, hD⟩

/-- Helper for Definition 17.29.8: the constructor above does not change the underlying morphism.
-/
@[simp] theorem diff_of_isDifferentialOperatorOfOrder_val
    (D : (restrictionAlong (inverseImageStructureSheafHomComm f)).obj ℱ ⟶
      (restrictionAlong (inverseImageStructureSheafHomComm f)).obj 𝒢)
    (hD : TopCat.Sheaf.IsDifferentialOperatorOfOrder (inverseImageStructureSheafHomComm f) D k) :
    (diff_of_isDifferentialOperatorOfOrder (f := f) (ℱ := ℱ) (𝒢 := 𝒢) (k := k) D hD).1 = D := by
  -- The subtype constructor stores `D` as its first component.
  rfl

end AlgebraicGeometry.RingedSpace
