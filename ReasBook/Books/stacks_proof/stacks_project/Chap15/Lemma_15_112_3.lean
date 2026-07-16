import stacks_proof.stacks_project.Chap15.Definition_15_112_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Ideal IsLocalRing IsExtensionOfDiscreteValuationRings

/-!
- primary domain: ramification and residue degrees in towers of discrete valuation rings
- sampled owner declarations:
  `IsExtensionOfDiscreteValuationRings.of_tower`,
  `IsExtensionOfDiscreteValuationRings.ramificationIndex`,
  `IsExtensionOfDiscreteValuationRings.residueDegree`,
  `IsExtensionOfDiscreteValuationRings.residueDegree_eq_inertiaDeg`,
  `Ideal.ramificationIdx_algebra_tower'`,
  `Ideal.inertiaDeg_algebra_tower`
- owner abstraction: the source-facing owners are
  `IsExtensionOfDiscreteValuationRings.ramificationIndex` and
  `IsExtensionOfDiscreteValuationRings.residueDegree`; the ideal-theoretic tower lemmas are the
  canonical core API used only to derive these source-facing formulas
- layer triage: this file is a `bridge/view` item from the ideal-theoretic tower lemmas to the
  chapter owners on extensions of discrete valuation rings
- primitive data: the algebra tower together with the two extension owners
  `IsExtensionOfDiscreteValuationRings A B` and `IsExtensionOfDiscreteValuationRings B C`
- derived API: the equalities comparing the chapter owners with
  `Ideal.ramificationIdx` and `Ideal.inertiaDeg`, where the ramification-index comparison is by
  direct unfolding of `ramificationIndex`
-/

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]

namespace IsExtensionOfDiscreteValuationRings

-- Proof sketch: derive the torsion-free instances from the injective extension owners, then
-- specialize `Ideal.ramificationIdx_algebra_tower'` to the maximal ideals in the DVR tower and
-- rewrite by unfolding the chapter owner `ramificationIndex`.
/-- Lemma 15.112.3: for extensions `A ⊂ B ⊂ C` of discrete valuation rings, the ramification
index from `A` to `C` is the product of the ramification indices from `A` to `B` and from `B` to
`C`. -/
@[stacks 0BRL]
theorem ramificationIndex_algebra_tower :
    ramificationIndex A C = ramificationIndex A B * ramificationIndex B C := by
  let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
  simpa [ramificationIndex] using
    ramificationIdx_algebra_tower' (maximalIdeal A) (maximalIdeal B) (maximalIdeal C)

-- Proof sketch: specialize `Ideal.inertiaDeg_algebra_tower` to the maximal ideals in the tower
-- `maximalIdeal A ⊂ maximalIdeal B ⊂ maximalIdeal C`; for discrete valuation rings these inertia
-- degrees are the residual degrees, so this gives multiplicativity for the chapter owner
-- `residueDegree` in the finite-residue-field case via `residueDegree_eq_inertiaDeg`.
/-- Lemma 15.112.3: for extensions `A ⊂ B ⊂ C` of discrete valuation rings, the residue degree
from `A` to `C` is the product of the residue degrees from `A` to `B` and from `B` to `C`. -/
@[stacks 0BRL]
theorem residueDegree_algebra_tower
    [FiniteDimensional (ResidueField A) (ResidueField B)]
    [FiniteDimensional (ResidueField B) (ResidueField C)] :
    let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
    let _ : FiniteDimensional (ResidueField A) (ResidueField C) :=
      FiniteDimensional.trans (ResidueField A) (ResidueField B) (ResidueField C)
    residueDegree A C = residueDegree A B * residueDegree B C := by
  let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
  let _ : FiniteDimensional (ResidueField A) (ResidueField C) :=
    FiniteDimensional.trans (ResidueField A) (ResidueField B) (ResidueField C)
  simpa [residueDegree_eq_inertiaDeg] using
    inertiaDeg_algebra_tower (maximalIdeal A) (maximalIdeal B) (maximalIdeal C)

end IsExtensionOfDiscreteValuationRings

end
