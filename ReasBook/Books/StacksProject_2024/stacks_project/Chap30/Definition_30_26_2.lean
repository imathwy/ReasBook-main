import StacksProject_2024.Chap30.Lemma_30_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open Scheme.IdealSheafData

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` returned `AlgebraicGeometry.IsProper`,
-- `AlgebraicGeometry.LocallyOfFiniteType`, and `Scheme.IdealSheafData.vanishingIdeal`.
-- Nearby Chapter 30 precedent represents a closed subset proper over a base by properness of
-- its reduced induced closed subscheme. The Stacks tag evidence is consistent for `0CYM`.

/-- Definition 30.26.2: for a locally finite type morphism `f : X ⟶ S`, a closed subset
`Z ⊆ X` is proper over `S` when the equivalent conditions of Lemma 30.26.1 hold; the
owner predicate records the reduced induced closed subscheme condition. -/
@[stacks 0CYM]
class ClosedSubset.IsProperOver
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (Z : TopologicalSpace.Closeds X) : Prop where
  /-- The reduced induced closed subscheme on `Z` is proper over the base. -/
  isProper : IsProper ((vanishingIdeal Z).subschemeι ≫ f)

namespace ClosedSubset.IsProperOver

/-- Specification for `ClosedSubset.IsProperOver`: the reduced induced closed subscheme on the
closed subset is proper over the base. -/
@[stacks 0CYM]
theorem isProper.spec
    {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    {Z : TopologicalSpace.Closeds X} [hZ : ClosedSubset.IsProperOver f Z] :
    IsProper ((vanishingIdeal Z).subschemeι ≫ f) := sorry

end ClosedSubset.IsProperOver

/-- Source-facing specification for the closed-subset properness predicate in terms of the
reduced induced closed subscheme. -/
@[stacks 0CYM]
theorem ClosedSubset.isProperOver_iff
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (Z : TopologicalSpace.Closeds X) :
    ClosedSubset.IsProperOver f Z ↔ IsProper ((vanishingIdeal Z).subschemeι ≫ f) := sorry

/-- A closed subset proper over the base supplies properness of its reduced induced closed
subscheme over that base. -/
instance ClosedSubset.instIsProperVanishingIdeal
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (Z : TopologicalSpace.Closeds X) [ClosedSubset.IsProperOver f Z] :
    IsProper ((vanishingIdeal Z).subschemeι ≫ f) := sorry

/-- Source-facing specification: the closed-subset predicate is equivalent to properness for
some, equivalently every, closed subscheme structure on the same underlying closed subset. -/
@[stacks 0CYM]
theorem ClosedSubset.isProperOver_tfae_closedSubschemeStructure
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (Z : TopologicalSpace.Closeds X) :
    List.TFAE [
      ClosedSubset.IsProperOver f Z,
      ∃ I : X.IdealSheafData, I.support = Z ∧ IsProper (I.subschemeι ≫ f),
      ∀ I : X.IdealSheafData, I.support = Z → IsProper (I.subschemeι ≫ f)
    ] := sorry

end AlgebraicGeometry
