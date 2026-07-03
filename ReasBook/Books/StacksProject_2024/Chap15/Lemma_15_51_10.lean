import Mathlib
import StacksProject_2024.Chap10.Lemma_10_165_6
import StacksProject_2024.Chap15.Lemma_15_51_3
import StacksProject_2024.Chap15.Lemma_15_51_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u

namespace FieldAlgebraProperty

section

variable (P : FieldAlgebraProperty)

/-- A field-algebra property has property `(E)` if it is preserved when the ground field is
replaced by a separable algebraic extension. -/
class HasPropertyE : Prop where
  /-- Base change of the ground field along a separable algebraic extension preserves `P`. -/
  separableBaseChange (k k' A : Type u) [Field k] [Field k'] [CommRing A]
      [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
      [Algebra.IsSeparable k k'] (hA : P k A) :
      P k' A

/- Domain sampling pass:
- primary domain: Chapter 15 formal-fiber axioms for `FieldAlgebraProperty`;
- sampled owner declarations:
  `FieldAlgebraProperty.HasPropertyA`,
  `FieldAlgebraProperty.HasPropertyB`,
  `FieldAlgebraProperty.HasPropertyC`,
  `FieldAlgebraProperty.HasPropertyD`;
- best owner abstraction: the chapter package extending `(A)` and `(B)` by the canonical upstream
  `(C)` and `(D)` owners from `Lemma_15_51_4`, together with the named bridge
  `IsGeometricallyNormalProperty`; this file adds only the genuinely new separable-base-field
  clause `(E)`.

Source/core/bridge triage:
- `P.HasPropertyE` is source-facing;
- `P.HasPropertiesABCDE` is the core/canonical owner wrapper;
- `IsGeometricallyNormalProperty` and the instance below are the thin bridge/view from
  `IsGeometricallyNormal` to that owner.
-/

/-- The five formal-fiber axioms `(A)` through `(E)` for a property of Noetherian algebras over
fields. -/
class HasPropertiesABCDE : Prop
    extends P.HasPropertyA, P.HasPropertyB, P.HasPropertyC, P.HasPropertyD, P.HasPropertyE

end

end FieldAlgebraProperty

namespace Algebra

section

/-- The canonical `FieldAlgebraProperty` bridge for geometric normality. -/
abbrev IsGeometricallyNormalProperty : FieldAlgebraProperty :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ IsGeometricallyNormal.{u, u} k A

section

variable {k k' A : Type u}
variable [Field k] [Field k'] [CommRing A]
variable [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]

-- Proof sketch: this is exactly the separable-base-field invariance theorem for geometric
-- normality from Lemma `10.165.6`, repackaged as Chapter 15 property `(E)` for the canonical
-- bridge `IsGeometricallyNormalProperty`.
/-- Lemma 15.51.10 (5), owner-form: geometric normality has property `(E)` in the Chapter 15
formal-fiber package. -/
instance isGeometricallyNormal_hasPropertyE :
    IsGeometricallyNormalProperty.HasPropertyE where
  separableBaseChange k k' A := by
    intro _ _ _ _ _ _ _ _ hA
    exact isGeometricallyNormal_iff_of_isSeparable.1 hA

end

-- Proof sketch: property `(A)` is immediate from the definition of geometric normality under
-- finitely generated base change. Property `(B)` is the local criterion for normality. Property
-- `(C)` is ascent of normality along regular maps on each fiber, using `Lemma 15.42.2`. Property
-- `(D)` is faithfully flat descent of normality on fibers, using `Lemma 10.164.3`. Property `(E)`
-- is invariance of geometric normality under separable algebraic extension of the ground field,
-- using `Lemma 10.165.6`.
/-- Lemma 15.51.10: the field-algebra property `IsGeometricallyNormal` satisfies the formal-fiber
axioms `(A)`, `(B)`, `(C)`, `(D)`, and `(E)`. -/
instance isGeometricallyNormal_hasPropertiesABCDE :
    IsGeometricallyNormalProperty.HasPropertiesABCDE where
  baseChange := by
    sorry
  localizationCriterion := by
    sorry
  regularAscent := by
    sorry
  closedFiberDescent := by
    sorry
  separableBaseChange := by
    intro k k' A _ _ _ _ _ _ _ _ hA
    exact isGeometricallyNormal_iff_of_isSeparable.1 hA

end

end Algebra
