import Mathlib.AlgebraicGeometry.ResidueField
import StacksProject_2024.stacks_project.Chap29.Definition_29_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` identified the canonical topological owners
-- `irreducibleComponents` and `genericPoints`, and Chapter 26 already uses the
-- canonical local-scheme morphism `Scheme.fromSpecStalk`.

/-- Lemma 29.50.3: let `f : X ⟶ Y` be a birational morphism of schemes such that both `X`
and `Y` have finitely many irreducible components. If `y : Y` is the generic point of an
irreducible component of `Y`, then the base change
`X ×[Y] Spec(\mathcal O_{Y, y}) ⟶ Spec(\mathcal O_{Y, y})` is an isomorphism. -/
@[stacks 0BAB]
theorem isIso_pullbackSnd_fromSpecStalk_of_isBirational
    {X Y : Scheme.{u}} [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    (f : X ⟶ Y) [IsBirational f] (y : genericPoints Y) :
    IsIso (pullback.snd f (Y.fromSpecStalk y)) := sorry

/-- Source-facing variant of `isIso_pullbackSnd_fromSpecStalk_of_isBirational` with an explicit
generic-point membership hypothesis. -/
theorem isIso_pullbackSnd_fromSpecStalk_of_isBirational_of_mem
    {X Y : Scheme.{u}} [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    (f : X ⟶ Y) [IsBirational f] {y : Y}
    (hy : y ∈ genericPointsOfIrreducibleComponents Y) :
    IsIso (pullback.snd f (Y.fromSpecStalk y)) := by
  simpa using isIso_pullbackSnd_fromSpecStalk_of_isBirational f ⟨y, hy⟩

end AlgebraicGeometry
