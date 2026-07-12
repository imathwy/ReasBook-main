import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Topology.Sober

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: this file is `source-facing` for the Stacks definition of birational
-- morphisms. The supporting generic-point owner is the canonical set `genericPoints X`, so the
-- chapter-local source-facing name is kept only as a thin bridge to that owner.

/-- The set of generic points of irreducible components of a scheme. -/
abbrev genericPointsOfIrreducibleComponents (X : Scheme.{u}) : Set X :=
  genericPoints X

namespace _root_.AlgebraicGeometry

/-- Source-facing Stacks notation for the generic points of irreducible components of a scheme. -/
scoped[AlgebraicGeometry] notation:max X:max "⁰" => genericPointsOfIrreducibleComponents X

end _root_.AlgebraicGeometry

/-- `genericPointsOfIrreducibleComponents` is the source-facing name for `genericPoints`. -/
theorem genericPointsOfIrreducibleComponents_eq_genericPoints (X : Scheme.{u}) :
    genericPointsOfIrreducibleComponents X = genericPoints X :=
  rfl

/-- Membership in `genericPointsOfIrreducibleComponents X` is membership in `genericPoints X`. -/
@[simp]
theorem mem_genericPointsOfIrreducibleComponents_iff (X : Scheme.{u}) (x : X) :
    x ∈ genericPointsOfIrreducibleComponents X ↔ x ∈ genericPoints X :=
  Iff.rfl

/-- Definition 29.50.1: assuming `X` and `Y` have finitely many irreducible components, a morphism
`f : X ⟶ Y` is birational if it induces a bijection on the generic points of irreducible
components and the induced map on each corresponding local ring is an isomorphism. The finiteness
assumptions from the source are omitted here because the generic-point formulation itself does not
depend on them. -/
@[stacks 01RO]
class IsBirational
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  bijOn_genericPointsOfIrreducibleComponents :
    Set.BijOn f.base X⁰ Y⁰
  isIso_stalkMap {η : X} :
    η ∈ X⁰ → IsIso (f.stalkMap η)

/-- Unfold `IsBirational f` into the generic-point bijection and local-ring isomorphism clauses of
Definition 29.50.1. -/
theorem isBirational_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsBirational f ↔
      Set.BijOn f.base X⁰ Y⁰ ∧
      ∀ {η : X}, η ∈ X⁰ → IsIso (f.stalkMap η) := by
  constructor
  · intro h
    exact ⟨h.bijOn_genericPointsOfIrreducibleComponents, h.isIso_stalkMap⟩
  · rintro ⟨hbij, hstalk⟩
    exact
      { bijOn_genericPointsOfIrreducibleComponents := hbij
        isIso_stalkMap := hstalk }

/-- A birational morphism induces a bijection on the canonical owner `genericPoints`. -/
theorem IsBirational.bijOn_genericPoints
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : IsBirational f) :
    Set.BijOn f.base (genericPoints X) (genericPoints Y) :=
  hf.bijOn_genericPointsOfIrreducibleComponents

/-- At a generic point of the source, a birational morphism induces an isomorphism on stalks. -/
theorem IsBirational.isIso_stalkMap_of_mem_genericPoints
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : IsBirational f) {η : X}
    (hη : η ∈ genericPoints X) :
    IsIso (f.stalkMap η) :=
  hf.isIso_stalkMap hη

/-- Subtype form of `IsBirational.isIso_stalkMap_of_mem_genericPoints`. -/
theorem IsBirational.isIso_stalkMap_genericPoint
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : IsBirational f) (η : genericPoints X) :
    IsIso (f.stalkMap η) :=
  hf.isIso_stalkMap_of_mem_genericPoints η.2

end AlgebraicGeometry
