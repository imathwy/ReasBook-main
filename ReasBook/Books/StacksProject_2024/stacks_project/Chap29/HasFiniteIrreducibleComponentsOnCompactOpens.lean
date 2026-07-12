import Mathlib.AlgebraicGeometry.Scheme

open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme belongs to this generalized rational-map setup when every quasi-compact open subset
has only finitely many irreducible components. The canonical owner for quasi-compact opens is
`CompactOpens X`. -/
class HasFiniteIrreducibleComponentsOnCompactOpens (X : Scheme.{u}) : Prop where
  /-- Every quasi-compact open subset of `X` has finitely many irreducible components. -/
  finite_irreducibleComponents (U : CompactOpens X) :
    (irreducibleComponents U).Finite

/-- Any compact open subset of a scheme with this property has finitely many irreducible
components as a type of components. -/
instance instFiniteIrreducibleComponentsCompactOpens (X : Scheme.{u})
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (U : CompactOpens X) :
    Finite (irreducibleComponents U) := by
  simpa using
    (HasFiniteIrreducibleComponentsOnCompactOpens.finite_irreducibleComponents U).to_subtype

end AlgebraicGeometry.Scheme
