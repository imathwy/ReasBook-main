import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical closed-point owner `closedPoints`,
-- the specialization theorem `IsLocalRing.specializes_closedPoint`, and the scheme predicate
-- `AlgebraicGeometry.IsLocallyNoetherian`. Local Chapter 5 precedent also uses `closedPoints X`
-- for closed points, so this item is stated directly on schemes and closed subsets of schemes.

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- Lemma 28.5.9 (1): any nonempty locally Noetherian scheme has a closed point. -/
theorem exists_closedPoint [Nonempty X] :
    Set.Nonempty (closedPoints X) := sorry

/-- Lemma 28.5.9 (2): any nonempty closed subset of a locally Noetherian scheme has a closed
point. -/
theorem exists_closedPoint_of_isClosed {Z : Set X} (hZ : IsClosed Z) (hZne : Z.Nonempty) :
    Set.Nonempty (closedPoints Z) := sorry

/-- Lemma 28.5.9 (3): any point of a locally Noetherian scheme specializes to a closed point. -/
theorem specializes_closedPoint (x : X) :
    ∃ y : X, x ⤳ y ∧ y ∈ closedPoints X := sorry

end AlgebraicGeometry.Scheme
