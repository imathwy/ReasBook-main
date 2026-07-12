import Mathlib.AlgebraicGeometry.FunctionField

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Source/core/bridge triage:
-- * `source-facing`: Definition 29.49.4 names the ring of rational functions on an arbitrary
--   scheme `X`.
-- * `core/canonical`: for integral schemes, Chapter 29 already uses `X.functionField` as the
--   canonical owner `R(X)`.
-- * `bridge/view`: in the general finite-component setting, the same Chapter 29 development
--   records rational functions through the canonical product of stalks at generic points.
--
-- The main owner here should therefore be that generic-point product ring, not an ambient
-- `[CommRing X.RationalFunction]` workaround binder.

/-- Definition 29.49.4: the ring of rational functions on `X` is the commutative ring whose
elements are recorded by the canonical product of the local rings at the generic points of the
irreducible components of `X`. -/
noncomputable abbrev rationalFunctionRing (X : Scheme.{u}) :
    CommRingCat :=
  CommRingCat.of (∀ η : genericPoints X, X.presheaf.stalk η.1)

namespace _root_.AlgebraicGeometry

scoped notation "R(" X ")" => Scheme.rationalFunctionRing X

end _root_.AlgebraicGeometry

/-- Unfold `X.rationalFunctionRing` as the product of the stalks at the generic points of `X`. -/
theorem rationalFunctionRing_def (X : Scheme.{u}) :
    rationalFunctionRing X =
      CommRingCat.of (∀ η : genericPoints X, X.presheaf.stalk η.1) :=
  rfl

private theorem eq_genericPoint_of_mem_genericPoints
    (X : Scheme.{u}) [IsIntegral X] (η : genericPoints X) :
    η.1 = genericPoint X := by
  simpa [genericPoints_eq_singleton] using η.2

private noncomputable abbrev genericPointAsGenericPoint
    (X : Scheme.{u}) [IsIntegral X] : genericPoints X :=
  ⟨genericPoint X, by simpa [genericPoints_eq_singleton] using genericPoint_spec X⟩

private theorem genericPoints_subsingleton
    (X : Scheme.{u}) [IsIntegral X] : Subsingleton (genericPoints X) :=
  ⟨fun η ξ ↦ Subtype.ext <|
    (eq_genericPoint_of_mem_genericPoints X η).trans
      (eq_genericPoint_of_mem_genericPoints X ξ).symm⟩

/-- For an integral scheme, the source-facing ring `R(X)` is canonically the function field
`X.functionField`. -/
noncomputable abbrev rationalFunctionRing_equiv_functionField
    (X : Scheme.{u}) [IsIntegral X] :
    rationalFunctionRing X ≃+* X.functionField where
  toFun f := f (genericPointAsGenericPoint X)
  invFun a := fun η ↦ by
    letI := genericPoints_subsingleton X
    let hη : η = genericPointAsGenericPoint X := Subsingleton.elim _ _
    cases hη
    exact a
  left_inv f := by
    letI := genericPoints_subsingleton X
    ext η
    have hη : η = genericPointAsGenericPoint X := Subsingleton.elim _ _
    cases hη
    rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end AlgebraicGeometry.Scheme
